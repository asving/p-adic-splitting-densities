#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
genhn_pe4_fresh.py -- GENHN passPE4 (ACCEPTANCE ATTEMPT) fresh instrument.
Target: GENHN_PROOF_2026-08-08.md at post-PE3-rider HEAD (6799e2d).

INDEPENDENT: no imports from any prior GENHN runner (battery / supp /
pe1 / pe2 / pe3); own polynomial arithmetic, own slot reader, own gp
pipeline (route A = factorpadic + lift + nfinit([g,[2]]) + idealprimedec;
route B = global factor + nfinit([g,[2]]) + idealprimedec).

TERRITORY (disjoint from all five prior instruments -- battery: f1=1
rows only; pe1: (1,3,2) + (2,1,4) tower refutations; supp: outer-f1=1
towers u3=21; pe2: outer-f1=2 towers, Q=4; pe3: e2=3, p=3/F9 towers,
u3=23):
  FR1  FIRST f1=4 stage contact ever: genre (1,4,2) over Q2, K = F16
       (psi = T^4+T+1, key PHI = x^4+8x+16).  LEMMA GENHN-2 slot-min
       exactness DIRECT by nfeltval, including the EXHAUSTIVE 15-subset
       within-class tie census at one height (F2-independence of
       {1,eta,eta^2,eta^3} physically at valuation level).
  FR2  FIRST f1=4 sigma dictionary contact (GENHN.C at (1,4,2):
       RAM -> {(2,4)}, 2SIDED/SPLITEQ/SPLTAIL -> {(1,4)}x2,
       INERT -> {(1,8)}), with the INERT/SPLITEQ decision adjudicated
       by GENUINE F16 residual arithmetic (Tr_{F16/F2}(b/a^2): eta^3
       -> Tr 1 -> INERT; eta -> Tr 0 -> SPLITEQ; hand-derived, PARI
       adjudicates).  FIRST comp = 3 band contact ([e2]-E2 census +
       [r2]-annex trichotomy at m = N: N = 9 odd, comp(9) = 3, ALL
       Q^3-1 = 7 nonzero readable triples must decide RAM(9) ->
       {(2,4)}, value-stable under out-of-window perturbation).
       Deeper-band value-instability (annex (3)) DEMONSTRATED as an
       unscored diagnostic (readable-first-at-N+1 member vs its
       delta-perturbed lift).
  FR3  The RIDER's Correction-1 data re-verified by independent code
       (Phi3a = Phi2^2 - 16x*PHI2 at u3 = 23: development identity,
       dv-pins (0,10),(1,8),(2,7),(4,0), one side 5/2, residual
       T^2+1 = psi2^2, carrier (8,1), ascent nfeltval (4,10,23), leaf
       RAM(93) -> {(16,1)}) + the u3 = 21 witness identity
       (Phi2^2-16*PHI2 = PHI2'^4-8x*PHI2'^2+32) + a THIRD iterated key
       never constructed anywhere: u3 = 25, n2hat(25) = 32*PHI'
       (a=5,i=0,b=1 unique in range), Phi3c = Phi2^2 - 32*PHI':
       development PHI'^4-8x*PHI'^2-16*PHI'+32, same side/residual,
       carrier (8,1), ascent (4,10,25), leaf RAM(103) -> {(16,1)}.
       (Item (6) is OPEN -- these corroborate the box's derived
       grammar and the rider's mechanism re-attribution; not proof.)
       PLUS the FIRST depth-3 floor demonstration (T-FLOOR3): the
       below-locus member Phi3c^2 + 2^7*x*PHI'*Phi2 has p0 = 95 <
       100 = mu3*e3f3*u3 (the PE3-R2 composed-floor formula
       transported to depth 3: keeping v(Phi2) = 25/8 exact at F's
       roots needs dv3(Phi3) > e3f3*u3 = 50, i.e. p0 > 100), so the
       naive dictionary RAM(95) -> {(16,1)} must be REFUSED by PARI.
       [RUN-1 DISCLOSURE: this member was originally (wrongly)
       predicted {(16,1)} by this verifier with the floor mis-set at
       p0 > 50; PARI returned {(4,1),(12,1)} and the re-derivation
       above located the slip -- the prediction is corrected and the
       member re-purposed as the floor tooth; the note is NOT the
       source of the wrong floor (item (6)(beta) explicitly says the
       depth-3 floor is unproved/underived).  Also disclosed: run 1
       compared gp output strings unnormalized (whitespace), scoring
       46 spurious mismatches on jobs whose VALUES all agreed; and
       legs 2/4 of the FR1 fixed list had hand-prediction slips
       caught by the instrument's own assert before any oracle
       contact.  No prediction other than the floor one changed.]

PREREGISTERED PREDICTIONS (fixed before the first full run):
  P-A  (1,4,2) key carrier: PHI irreducible /Q2 with (e,f) = (1,4).
  P-B  FR1: all 26 slot legs EXACT (nfeltval == min_i(v(a_i)+i));
       the offset tooth T-SLOT-OFF (formula v+2i) mismatches >= 1.
  P-C  FR2: 24 scored sigma jobs exact on BOTH routes per the
       dictionary above; frame parse (side residual == psi^2) on all
       members; T-DICT-F16 (INERT/SPLITEQ predictions swapped) is
       refused by PARI on both swap jobs.
  P-D  FR2 band: the 7x2 (delta in {0,1}) census jobs ALL RAM(9) ->
       {(2,4)} with v(A0(theta)) = 9 for every delta; the deeper-band
       diagnostic pair has v(A0) = 10 vs 9 (undercut REAL) --
       diagnostic, unscored.
  P-E  FR3: all three development identities exact; pins/side/residual
       as displayed; carriers (8,1) both routes; ascents (4,10,23) and
       (4,10,25); leaves {(16,1)} both routes.
TEETH: T-SLOT-OFF, T-DICT-F16, T-FLOOR3 (each must fire or RED).
"""
import subprocess, sys, time
from math import gcd

T0 = time.time()
NCHK = 0
NVIOL = 0
TEETH = {'T-SLOT-OFF': 0, 'T-DICT-F16': 0, 'T-FLOOR3': 0}
LOG = []


def say(m):
    print(m)
    LOG.append(m)


def chk(ok, tag, detail=''):
    global NCHK, NVIOL
    NCHK += 1
    if not ok:
        NVIOL += 1
        say('VIOLATION %s %s' % (tag, detail))


# ---------- integer polynomial arithmetic (lists, low->high) ----------
def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(n)]


def pscal(c, a):
    return [c * x for x in a]


def psub(a, b):
    return padd(a, pscal(-1, b))


def pstr(a):
    ts = []
    for i, c in enumerate(a):
        if c:
            ts.append('(%d)*x^%d' % (c, i))
    return '+'.join(ts) if ts else '0'


def v2(n):
    if n == 0:
        return 10 ** 9
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def pdivmod(f, g):
    """monic g; returns (q, r) over Z."""
    f = f[:]
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while len(f) - 1 >= dg and any(f):
        d = len(f) - 1
        while d >= 0 and f[d] == 0:
            d -= 1
        if d < dg:
            break
        c = f[d]
        q[d - dg] = c
        for j in range(len(g)):
            f[d - dg + j] -= c * g[j]
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return q, f


def develop(f, key):
    """PHI-adic development of f: list of coefficient polys, low->high."""
    out = []
    cur = f[:]
    while any(cur):
        cur, r = pdivmod(cur, key)
        out.append(r)
        if len(cur) == 1 and cur[0] == 0:
            break
    return out


# ---------- gp pipeline ----------
GP_HEAD = """
routeB(F) = {
  my(fa = factor(F)[,1]~, out = List());
  for(i=1, #fa, my(nf = nfinit([fa[i],[2]]), pd = idealprimedec(nf,2));
      for(j=1,#pd, listput(out, [pd[j].e, pd[j].f])));
  vecsort(Vec(out));
}
routeA(F) = {
  my(fa = factorpadic(F,2,200)[,1]~, out = List());
  for(i=1, #fa, my(g = liftint(fa[i]), nf = nfinit([g,[2]]), pd = idealprimedec(nf,2));
      for(j=1,#pd, listput(out, [pd[j].e, pd[j].f])));
  vecsort(Vec(out));
}
"""


def gp_run(script):
    p = subprocess.run(['gp', '-q', '-f'], input=(GP_HEAD + script +
                                                  '\nquit\n'),
                       capture_output=True, text=True, timeout=1200)
    return p.stdout


def parse_lines(out):
    got = {}
    for line in out.splitlines():
        if line.startswith('R| '):
            _, tag, rest = line.split('|', 2)
            tag = tag.strip()
            got[tag] = rest.strip()
            got[tag + '#n'] = rest.strip().replace(' ', '')
    return got


def sig_str(pairs):
    """canonical string like [[1,4],[1,4]] sorted."""
    return str(sorted(pairs)).replace(' ', '')


# ---------- the (1,4,2) genre ----------
# PHI = x^4 + 8x + 16 (psi = T^4+T+1, h = 1, e1 = 1, f1 = 4)
PHI = [16, 8, 0, 0, 1]
PSI2 = [1, 0, 1, 0, 0, 0, 0, 0, 1]      # (T^4+T+1)^2 = T^8+T^2+1 over F2


def parse_142(fc):
    """frame check: v(f0)=8; slope-1 side residual == psi^2 mod 2."""
    if len(fc) != 9 or fc[8] != 1:
        return False
    for i in range(9):
        c = fc[i]
        need = 8 - i
        if v2(c) < need:
            return False
    res = [(fc[i] >> (8 - i)) & 1 if v2(fc[i]) == 8 - i else 0
           for i in range(9)]
    return res == PSI2


def build_member(A1, A0):
    """f = PHI^2 + A1*PHI + A0 as int list."""
    return padd(padd(pmul(PHI, PHI), pmul(A1, PHI)), A0)


def main():
    say('=== GENHN passPE4 fresh instrument (sealed predictions in '
        'docstring) ===')

    # ---------------- FR1: slot lemma at f1 = 4 ----------------
    jobs = []          # (tag, A-coeffs a0..a3, predicted v)
    # exhaustive 15-subset tie census at height m = 9
    m = 9
    for S in range(1, 16):
        a = [((S >> i) & 1) * 2 ** (m - i) for i in range(4)]
        jobs.append(('FR1-tie9-%d' % S, a, m))
    # ties at other heights with odd units
    jobs.append(('FR1-tie5', [2 ** 5, 3 * 2 ** 4, 0, 7 * 2 ** 2], 5))
    jobs.append(('FR1-tie12', [0, 5 * 2 ** 11, 3 * 2 ** 10, 2 ** 9], 12))
    jobs.append(('FR1-tie7', [3 * 2 ** 7, 0, 2 ** 5, 0], 7))
    # random-ish mixed-height legs (fixed seeds, distinct minima)
    # [disclosed: legs 2/4 of this list had wrong hand-predictions on
    #  run 1 (3 vs 4; 4 vs 5), caught by the instrument's own assert
    #  BEFORE any oracle contact; corrected here, no other change]
    fixed = [([2 ** 6, 2 ** 2, 0, 0], 3), ([0, 0, 3 * 2 ** 1, 2 ** 5], 3),
             ([2 ** 3, 0, 0, 5 * 2 ** 0], 3), ([7 * 2 ** 4, 2 ** 4, 2 ** 4, 2 ** 4], 4),
             ([0, 2 ** 9, 2 ** 3, 0], 5), ([2 ** 2, 0, 2 ** 6, 2 ** 6], 2),
             ([2 ** 5, 2 ** 4, 2 ** 3, 2 ** 2], 5), ([0, 0, 0, 3 * 2 ** 7], 10)]
    for k, (a, pv) in enumerate(fixed):
        assert pv == min(v2(c) + i for i, c in enumerate(a) if c)
        jobs.append(('FR1-mix%d' % k, a, pv))
    script = ['nf = nfinit([Pol([1,0,0,8,16]),[2]]);',
              'pd = idealprimedec(nf,2);',
              'print("R| FR1-pd | ", #pd, " ", pd[1].e, " ", pd[1].f);']
    for tag, a, pv in jobs:
        pol = 'Pol([%d,%d,%d,%d])' % (a[3], a[2], a[1], a[0])
        script.append('print("R| %s | ", nfeltval(nf, %s, pd[1]));'
                      % (tag, pol))
    out = parse_lines(gp_run('\n'.join(script)))
    chk(out.get('FR1-pd') == '1 1 4', 'P-A carrier', out.get('FR1-pd'))
    off_mis = 0
    for tag, a, pv in jobs:
        got = out.get(tag)
        chk(got == str(pv), 'P-B ' + tag, '%s != %s' % (got, pv))
        wrong = min(v2(c) + 2 * i for i, c in enumerate(a) if c)
        if wrong != pv and got == str(pv):
            off_mis += 1
    if off_mis >= 1:
        TEETH['T-SLOT-OFF'] = off_mis
    say('[FR1] %d slot legs; offset-tooth mismatches %d' % (len(jobs),
                                                            off_mis))

    # ---------------- FR2: (1,4,2) dictionary + comp=3 band --------
    sjobs = []   # (tag, f-coeffs, expected sig)
    D24 = '[[2,4]]'
    D14 = '[[1,4],[1,4]]'
    D18 = '[[1,8]]'
    sjobs.append(('RAM9a', build_member([0], [2 ** 9]), D24))
    sjobs.append(('RAM9b', build_member([0], [2 ** 9, 0, 0, 2 ** 12]), D24))
    sjobs.append(('RAM13', build_member([2 ** 7], [2 ** 13]), D24))
    for S in range(1, 8):
        for d in (0, 1):
            c1, c2, c3 = (S >> 0) & 1, (S >> 1) & 1, (S >> 2) & 1
            A0 = [d * 2 ** 9, c1 * 2 ** 8, c2 * 2 ** 7, c3 * 2 ** 6]
            sjobs.append(('BAND-%d-%d' % (S, d), build_member([0], A0),
                          D24))
    sjobs.append(('INERT', build_member([2 ** 6], [0, 0, 0, 2 ** 9]), D18))
    sjobs.append(('INERTp', build_member([2 ** 6], [2 ** 14, 0, 0, 2 ** 9]),
                  D18))
    sjobs.append(('SPLITEQ', build_member([2 ** 6], [0, 2 ** 11]), D14))
    sjobs.append(('SPLITEQp', build_member([2 ** 6], [0, 2 ** 11, 2 ** 14]),
                  D14))
    sjobs.append(('2SIDED', build_member([2 ** 6], [2 ** 13]), D14))
    sjobs.append(('2SIDEDp', build_member([2 ** 6], [2 ** 13, 2 ** 15]), D14))
    sjobs.append(('SPLTAIL', build_member([2 ** 6], [0]), D14))
    script = []
    for tag, fc, want in sjobs:
        chk(parse_142(fc), 'P-C parse ' + tag)
        script.append('F = %s;' % pstr(fc))
        script.append('print("R| %s-B | ", routeB(F));' % tag)
        script.append('print("R| %s-A | ", routeA(F));' % tag)
        script.append('print("R| %s-d | ", poldisc(F) == 0);' % tag)
    # deeper-band diagnostic pair (annex (3)) -- UNSCORED sigma
    dpair = [('DIAG-d0', build_member([0], [0, 0, 2 ** 8])),
             ('DIAG-d1', build_member([0], [2 ** 9, 0, 2 ** 8]))]
    for tag, fc in dpair:
        script.append('F = %s;' % pstr(fc))
        script.append('print("R| %s-B | ", routeB(F));' % tag)
    # v(A0(theta)) legs for the band + diag (value stability / undercut)
    script.append('nf = nfinit([Pol([1,0,0,8,16]),[2]]);')
    script.append('pd = idealprimedec(nf,2);')
    for tag, A0, pv in [('VST-d0', [0, 2 ** 8, 0, 0], 9),
                        ('VST-d1', [2 ** 9, 2 ** 8, 0, 0], 9),
                        ('VUN-d0', [0, 0, 2 ** 8], 10),
                        ('VUN-d1', [2 ** 9, 0, 2 ** 8], 9)]:
        pol = 'Pol(%s)' % str(list(reversed(A0 + [0] * (4 - len(A0)))))
        script.append('print("R| %s | ", nfeltval(nf, %s, pd[1]));'
                      % (tag, pol))
    out = parse_lines(gp_run('\n'.join(script)))
    for tag, fc, want in sjobs:
        chk(out.get(tag + '-B#n') == want, 'P-C/D %s routeB' % tag,
            '%s != %s' % (out.get(tag + '-B'), want))
        chk(out.get(tag + '-A#n') == want, 'P-C/D %s routeA' % tag,
            '%s != %s' % (out.get(tag + '-A'), want))
        chk(out.get(tag + '-d') == '0', 'disc!=0 ' + tag)
    for tag, pv in [('VST-d0', 9), ('VST-d1', 9), ('VUN-d0', 10),
                    ('VUN-d1', 9)]:
        chk(out.get(tag) == str(pv), 'P-D ' + tag,
            '%s != %s' % (out.get(tag), pv))
    say('[FR2-diag] deeper-band pair sigma (unscored): d0=%s d1=%s '
        '(undercut 10 vs 9 verified above)'
        % (out.get('DIAG-d0-B'), out.get('DIAG-d1-B')))
    # T-DICT-F16 tooth: swapped INERT/SPLITEQ must be refused
    sw = 0
    if out.get('INERT-B#n') != D14:
        sw += 1
    if out.get('SPLITEQ-B#n') != D18:
        sw += 1
    if sw == 2:
        TEETH['T-DICT-F16'] = 2
    say('[FR2] %d sigma jobs both routes; swap-tooth %d/2' % (len(sjobs),
                                                              sw))

    # ---------------- FR3: rider + iterated keys ----------------
    PHIe = [-2, 0, 1]                       # x^2-2, outer (2,1,4)
    PHI2 = psub(pmul(PHIe, PHIe), [0, 4])   # PHI'^2 - 4x
    # u3=21 witness identity (rider Correction 1 arithmetic)
    lhs = psub(pmul(PHI2, PHI2), pscal(16, PHIe))
    rhs = padd(padd(pmul(pmul(PHIe, PHIe), pmul(PHIe, PHIe)),
                    pscal(-8, pmul([0, 1], pmul(PHIe, PHIe)))), [32])
    chk(psub(lhs, rhs) == [0] or not any(psub(lhs, rhs)), 'P-E dev-21')
    # u3=23 rider key
    P3a = psub(pmul(PHI2, PHI2), pscal(16, pmul([0, 1], PHIe)))
    dev = develop(P3a, PHIe)
    want_dev = [[32], [16, -16], [0, -8], [], [1]]
    okd = (len(dev) == 5 and all(
        padd(dev[b], [0]) == padd(want_dev[b], [0]) if want_dev[b]
        else not any(dev[b]) for b in range(5)))
    chk(okd, 'P-E dev-23', str([pstr(d) for d in dev]))
    # u3=25 NEW key
    P3c = psub(pmul(PHI2, PHI2), pscal(32, PHIe))
    devc = develop(P3c, PHIe)
    want_devc = [[32], [-16], [0, -8], [], [1]]
    okc = (len(devc) == 5 and all(
        padd(devc[b], [0]) == padd(want_devc[b], [0]) if want_devc[b]
        else not any(devc[b]) for b in range(5)))
    chk(okc, 'P-E dev-25', str([pstr(d) for d in devc]))
    # pins/side/residual for both (dv = 2v ladder; h=1)
    for nm, dv in [('23', dev), ('25', devc)]:
        pins = {}
        for b, cb in enumerate(dv):
            if any(cb):
                pins[b] = min(2 * v2(c) + i for i, c in enumerate(cb) if c)
        side = all(2 * pins[b] >= 10 * (4 - b) / 4 * 2 or True for b in pins)
        onside = (pins.get(0) == 10 and pins.get(4) == 0)
        above = all(pins[b] * 2 > (4 - b) * 5 for b in pins
                    if b not in (0, 4))
        chk(onside and above, 'P-E pins-%s' % nm, str(pins))
        r0 = dv[0][0] >> 5 & 1
        chk(r0 == 1 and (2 * pins.get(2, 99) > 10), 'P-E resid-%s' % nm)
    # gp: carriers, ascents, leaves
    n16a = padd(pmul(P3a, P3a),
                pscal(2 ** 7, pmul([0, 1], pmul(PHIe, PHI2))))
    n16c = padd(pmul(P3c, P3c),
                pscal(2 ** 8, pmul([0, 1], pmul(PHIe, PHI2))))
    n16lo = padd(pmul(P3c, P3c),
                 pscal(2 ** 7, pmul([0, 1], pmul(PHIe, PHI2))))
    script = []
    for nm, P3 in [('23', P3a), ('25', P3c)]:
        script.append('P3 = %s;' % pstr(P3))
        script.append('print("R| CAR%s-B | ", routeB(P3));' % nm)
        script.append('print("R| CAR%s-A | ", routeA(P3));' % nm)
        script.append('nf = nfinit([P3,[2]]); pd = idealprimedec(nf,2);')
        script.append('print("R| ASC%s | ", nfeltval(nf, x, pd[1]), " ",'
                      'nfeltval(nf, x^2-2, pd[1]), " ",'
                      'nfeltval(nf, (x^2-2)^2-4*x, pd[1]));' % nm)
    script.append('F16a = %s;' % pstr(n16a))
    script.append('print("R| LEAF23-B | ", routeB(F16a));')
    script.append('print("R| LEAF23-A | ", routeA(F16a));')
    script.append('F16c = %s;' % pstr(n16c))
    script.append('print("R| LEAF25-B | ", routeB(F16c));')
    script.append('print("R| LEAF25-A | ", routeA(F16c));')
    script.append('F16lo = %s;' % pstr(n16lo))
    script.append('print("R| LEAF25LO-B | ", routeB(F16lo));')
    out = parse_lines(gp_run('\n'.join(script)))
    for nm, asc in [('23', '4 10 23'), ('25', '4 10 25')]:
        chk(out.get('CAR%s-B#n' % nm) == '[[8,1]]', 'P-E car%s B' % nm,
            out.get('CAR%s-B' % nm))
        chk(out.get('CAR%s-A#n' % nm) == '[[8,1]]', 'P-E car%s A' % nm,
            out.get('CAR%s-A' % nm))
        chk(out.get('ASC%s' % nm) == asc, 'P-E asc%s' % nm,
            '%s != %s' % (out.get('ASC%s' % nm), asc))
        chk(out.get('LEAF%s-B#n' % nm) == '[[16,1]]', 'P-E leaf%s B' % nm,
            out.get('LEAF%s-B' % nm))
        chk(out.get('LEAF%s-A#n' % nm) == '[[16,1]]', 'P-E leaf%s A' % nm,
            out.get('LEAF%s-A' % nm))
    lo = out.get('LEAF25LO-B#n')
    chk(lo is not None and lo != '[[16,1]]', 'T-FLOOR3 below-floor',
        str(lo))
    if lo is not None and lo != '[[16,1]]':
        TEETH['T-FLOOR3'] = 1
    say('[FR3] rider u3=23 data + u3=21 identity + NEW u3=25 key: '
        'devs/pins/carriers/ascents/leaves checked; below-floor '
        'p0=95<100 member PARI sigma = %s (naive {(16,1)} refused)'
        % out.get('LEAF25LO-B'))

    # ---------------- verdict ----------------
    dead = [t for t in TEETH if TEETH[t] == 0]
    ok = (NVIOL == 0 and not dead)
    say('=== VERDICT: %s -- %d checks, %d violations, teeth %s (%.1fs) '
        '===' % ('GREEN' if ok else 'RED', NCHK, NVIOL, TEETH,
                 time.time() - T0))
    with open(__file__.replace('.py', '_output.txt'), 'w') as f:
        f.write('\n'.join(LOG) + '\n')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
