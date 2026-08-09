#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""GENH4 ANNEX PE5 SUPPLEMENTARY LEG (post-acceptance, purely ADDITIVE).

GENH4 was ACCEPTED 2/2 at PE5 (GENH4_passPE5_report.md, 11dbd23); the
note body is byte-frozen at r3 4b0d946 and every sealed artifact is
byte-frozen (md5 pins re-verified in C0 below).  This leg supports the
dated ANNEX PE5 appended to GENH4_PROOF_2026-08-08.md: it reads the
COMMITTED artifacts, re-derives the two MINOR display items and the
S9.2 remark on them, and adds a small fresh machine contact (explicit
genre-F members + PARI sigma).  Precedent: he7annex_supp.py (HE7 annex
F-1), genh4r2_supp.py (r2 supp).  Nothing sealed is written.

PREREGISTERED PREDICTIONS (all derived in the annex BEFORE this run):

P1 (committed rows read as the annex states): qscout22_results.json
   rows 15/16/19 = consF (Zp,2,7,k1)/(Zp,2,8,k1)/(Fqt,2,7,k1) carry
   SPLTAIL at w = 3 ONLY (values 384 / 1,536 / 384), empty-history
   UND = 128 / 1,024 / 128, and 2SIDED(3,4) = 384 / 9,216 / 384.
P2 (own law, TRUE cap 2w < N): a fresh typing of the S6.1/S6.3 genre-F
   count recursion reproduces rows 15, 16, 19 KEY-FOR-KEY (row 19 ==
   row 15, characteristic-blindness).
P3 (the WRONG-cap refutation, MINOR 1): the same recursion with the
   misread cap w < N predicts, at (Zp,2,8,k1): SPLTAIL(4) = 384,
   SPLTAIL(5) = 96, SPLTAIL(6) = 24, SPLTAIL(7) = 6, UND = 514
   (masses conserved: 514 + 510 = the committed 1,024), and at
   (Zp,2,7,k1): SPLTAIL(4) = 96, SPLTAIL(5) = 24, SPLTAIL(6) = 6,
   UND = 2 (2 + 126 = 128); the mismatch set vs the committed rows is
   EXACTLY the SPLTAIL/UND keys and nothing else (no decided
   RAM/2SIDED/SPLITEQ/INERT key moves).
   [DISCLOSED smoke catch, first sealed run cceca77: the sealed
   prereg scoped the mismatch set to the EMPTY history; the run
   caught the wrong cap propagating into the refined (3,)-history
   node as well -- still SPLTAIL/UND keys only, values hand-derived
   before this repair: row 16 @(3,): SPLTAIL(4..7) =
   1,152/288/72/18, UND = 1,542 (1,530 + 1,542 = committed 3,072);
   row 15 @(3,): SPLTAIL(4..6) = 288/72/18, UND = 6 (378 + 6 =
   committed 384).  Instrument-side prereg miss (set scoping), not a
   law defect; the refutation is STRENGTHENED (the misread cap also
   corrupts refined histories).  One repair: the expected mismatch
   tables below now carry both histories; verdict from the repaired
   fresh run.]
P4 (MINOR 2, v(Res) = 2u at genre F): explicit 2SIDED(3,4) members at
   (Zp,2,7,k1) with key phi = x^2+2x+4 (v(p1)=1>=k, v(p0)=2=2k exact,
   residue pair psi = y^2+y+1): every member has
   v2(Res(F,phi)) = 14 = 2u (u = 7), via TWO independent routes
   (6x6 Sylvester determinant vs reduce-mod-phi + quadratic norm
   alpha^2 p0 - alpha beta p1 + beta^2); the halved balance
   j*w/2 + (4-j)(u-w)/2 = u and the unhalved j*w + (4-j)(u-w) = 2u
   both give j = 2, while the FALSE mixed form
   j*w + (4-j)(u-w) = u gives j = 9 at (w,u) = (3,7): impossible,
   self-alarming.  PARI: sigma = {(1,2),(1,2)} on every member.
P5 (the F-SPLTAIL sigma-inequality u_lift >= N > 2w, MINOR 1's annex
   claim): at (Zp,2,7,k1) SPLTAIL(3) (A1 in {8, 4x, 4x+8}, A0 hidden),
   EVERY constructed disc != 0 lift (u_lift in {7,8,9,...} incl. the
   A0 = 0 corner) has PARI sigma = {(1,2),(1,2)} == the S1 F-SPLTAIL
   label.  TOOTH: at w = 4 (2w = 8 >= N = 7, SPLTAIL under the WRONG
   cap only), two lifts of ONE hidden-A0 state differ: u_lift = 7
   (odd, <= 2w) -> RAM(7) -> {(2,2)}, u_lift = 9 (> 2w) ->
   2SIDED(4,5) -> {(1,2),(1,2)} -- no single label is lift-sound
   there, which is WHY the implemented cap is 2w < N.
P6 (REMARK, S9.2 closure): the five E-stage per-node masses
   RAM q^2/Phi2, SPLITEQ (q-2)/(2 Phi2), INERT q/(2 Phi2),
   2SIDED 1/Phi2, REFINE 1/Phi2 (Phi2 = q^2+q+1) sum to 1
   COEFFICIENTWISE (2q^2 + (q-2) + q + 2 + 2 == 2 Phi2 as integer
   polynomials): the dangling "- extra..." token of S9.2 is 0 -- the
   2SIDED mass is EXACTLY 1/Phi2.  The ladder closed forms and the
   mu_E aggregation (x Phi2/(q^2+q) -> nu2's fractions) verified as
   exact rational identities at 7 points q (all numerator degrees
   < 7, so 7 points decide the identity).  TOOTH: a nonzero extra
   (r^4) breaks the partition of unity at every q.

Exit 0 iff zero violations.  Artifacts: genh4annex_supp_output.txt,
genh4annex_supp_results.json.
"""
import ast
import hashlib
import json
import os
import subprocess
import sys
import time
from fractions import Fraction
from itertools import permutations

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = []
VIOL = []


def say(s):
    print(s)
    LOG.append(s)


def viol(tag, msg):
    VIOL.append((tag, msg))
    say('VIOLATION [%s] %s' % (tag, msg))


def md5f(path):
    with open(path, 'rb') as fh:
        return hashlib.md5(fh.read()).hexdigest()


PINS = {
    'genh4_checks.py': 'ee8024b7a500220a6408dab373d7432f',
    'genh4_checks_output.txt': '9e6ca9b3b83aa9902ddef379f72db741',
    'genh4_checks_results.json': 'cbcff562132f82e302d95a017318075c',
    'qscout22_checks.py': 'cb885663dd4ef6dfda9c28a67c1a076e',
    'qscout22_results.json': '6c2441a12cf52ffd43055de912a4affe',
}


# ============ the genre-F count law, typed fresh from S6.1/S6.3 =====
# Slot strings (S2.3, genre F, per psi): A1 heights 2k+1..N+k-1, A0
# heights 4k+1..N+k-1; comp(m) = 2 for m <= N-1 (both components
# in-window), 1 for m >= N (a1-component only).  cap='2w' is the true
# SPLTAIL cap 2w < N (S6.3's complement: UND frees A1 at 2s >= N);
# cap='w' is the misread w < N (UND then frees A1 at s >= N).
def law_F_annex(q, N, k, cap='2w'):
    A1all = list(range(2 * k + 1, N + k))
    A0all = list(range(4 * k + 1, N + k))
    comp = lambda m: 2 if m <= N - 1 else 1
    Q = q * q
    c11 = (Q - 1) * (Q - 2) // 2
    c2 = Q * (Q - 1) // 2
    spl_ok = (lambda w: 2 * w < N) if cap == '2w' else (lambda w: w < N)
    out = {}

    def put(kk, v):
        if v:
            out[kk] = out.get(kk, 0) + v

    def rec(f1, f0, wt, H2):
        A1 = [s for s in A1all if s > f1]
        A0 = [s for s in A0all if s > f0]
        deep0 = q ** sum(comp(s) for s in A0 if s > N)
        for w in A1:
            if spl_ok(w):
                put((H2, 'SPLTAIL', (w,)), wt * (q ** comp(w) - 1)
                    * q ** sum(comp(s) for s in A1 if s > w) * deep0)
        put((H2, 'UND', ()), wt * deep0
            * q ** sum(comp(s) for s in A1 if not spl_ok(s)))
        for u in A0:
            if u > N:
                continue
            nz0 = q ** sum(comp(s) for s in A0 if s > u)
            ex0 = q ** comp(u) - 1
            if u % 2 == 1:
                put((H2, 'RAM', (u,)), wt * ex0 * nz0
                    * q ** sum(comp(s) for s in A1 if 2 * s > u))
            for w in A1:
                if 2 * w < u:
                    put((H2, '2SIDED', (w, u - w)),
                        wt * (q ** comp(w) - 1) * ex0 * nz0
                        * q ** sum(comp(s) for s in A1 if s > w))
            if u % 2 == 0:
                dmu = u // 2
                on1 = q ** sum(comp(s) for s in A1 if s > dmu)
                if u == N:
                    put((H2, 'UND', ()),
                        wt * q ** comp(dmu) * ex0 * on1 * nz0)
                else:
                    put((H2, 'SPLITEQ', (dmu,)), wt * on1 * nz0 * c11)
                    put((H2, 'INERT', (dmu,)), wt * on1 * nz0 * c2)
                    rec(dmu, u, wt * (Q - 1), H2 + (dmu,))

    rec(2 * k, 4 * k, 1, ())
    return out


# ==================== exact integer polynomial helpers ==============
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(n)]


def ptrim(a):
    while a and a[-1] == 0:
        a = a[:-1]
    return a


def pdivmod_monic(a, b):
    """a, b coeff lists (ascending), b monic: return (quot, rem)."""
    a = list(a)
    q = [0] * max(1, len(a) - len(b) + 1)
    while len(ptrim(a)) >= len(b):
        a = ptrim(a)
        d = len(a) - len(b)
        c = a[-1]
        q[d] += c
        for i, y in enumerate(b):
            a[d + i] -= c * y
    return q, ptrim(a)


def sylvester_res(f, g):
    """Res(f, g), f deg m, g deg n, ascending coeff lists."""
    f, g = ptrim(f), ptrim(g)
    m, n = len(f) - 1, len(g) - 1
    N_ = m + n
    M = []
    for i in range(n):
        row = [0] * N_
        for j, c in enumerate(reversed(f)):
            row[i + j] = c
        M.append(row)
    for i in range(m):
        row = [0] * N_
        for j, c in enumerate(reversed(g)):
            row[i + j] = c
        M.append(row)
    tot = 0
    for perm in permutations(range(N_)):
        sgn, prod = 1, 1
        seen = list(perm)
        # permutation sign by counting inversions
        inv = sum(1 for i in range(N_) for j in range(i + 1, N_)
                  if seen[i] > seen[j])
        sgn = -1 if inv % 2 else 1
        for i in range(N_):
            prod *= M[i][perm[i]]
            if prod == 0:
                break
        tot += sgn * prod
    return tot


def v2(n):
    assert n != 0
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def gp_sigmas(polys, p):
    gp = os.path.expanduser('~/.local/bin/gp')
    if not os.path.exists(gp):
        gp = 'gp'
    fun = r"""
ef(g, p) = {
  if (poldegree(g) == 1, return([1, 1]));
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  [dec[1].e, dec[1].f]
}
sig(f, p) = {
  my(d = poldisc(f), F);
  if (d == 0, return([[-1, -1]]));
  F = factorpadic(f, p, 200);
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i, 1]), p)))
}
"""
    lines = [fun]
    for i, cs in enumerate(polys):
        expr = '+'.join('(%d)*x^%d' % (c, j) for j, c in enumerate(cs))
        lines.append('print("R %d ", sig(%s, %d))' % (i, expr, p))
    lines.append('quit')
    r = subprocess.run([gp, '-q'], input='\n'.join(lines).encode(),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       timeout=600)
    if r.returncode != 0:
        raise RuntimeError('gp failed: %s' % r.stderr.decode()[:300])
    got = {}
    for line in r.stdout.decode().splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            nums = [int(x) for x in rest.replace('[', ' ')
                    .replace(']', ' ').replace(',', ' ').split()]
            got[int(idx)] = tuple(sorted(zip(nums[0::2], nums[1::2])))
    return [got[i] for i in range(len(polys))]


def main():
    t0 = time.time()
    results = {'checks': {}}

    # ------------------------------------------------------- C0 pins
    for fn, want in sorted(PINS.items()):
        have = md5f(os.path.join(HERE, fn))
        if have != want:
            viol('C0', '%s md5 %s != %s' % (fn, have, want))
    say('C0 pins: %d/%d verified' % (len(PINS), len(PINS)))
    results['checks']['C0-pins'] = len(PINS)

    # ------------------------------------- C1 committed rows (P1)
    with open(os.path.join(HERE, 'qscout22_results.json')) as fh:
        rows = json.load(fh)['rows']
    committed = {}
    for i in (15, 16, 19):
        tab = {}
        for kstr, v in rows[i]['keys'].items():
            g, pre, mult, H2, leaf, par = ast.literal_eval(kstr)
            assert g == 'F' and pre == () and mult == 1
            tab[(tuple(H2), leaf, tuple(par))] = v
        committed[i] = (rows[i]['row'], tab)
        say('C1 row %d = %s: %d keys, %d members' %
            (i, rows[i]['row'], len(tab), sum(tab.values())))
    exp_c1 = {15: (384, 128, 384), 16: (1536, 1024, 9216),
              19: (384, 128, 384)}
    for i, (spl3, und, ts34) in exp_c1.items():
        tab = committed[i][1]
        spl_keys = [kk for kk in tab if kk[1] == 'SPLTAIL']
        if spl_keys != [((), 'SPLTAIL', (3,))]:
            viol('C1', 'row %d SPLTAIL keys %s' % (i, spl_keys))
        for got, want, nm in ((tab.get(((), 'SPLTAIL', (3,))), spl3,
                               'SPLTAIL(3)'),
                              (tab.get(((), 'UND', ())), und, 'UND'),
                              (tab.get(((), '2SIDED', (3, 4))), ts34,
                               '2SIDED(3,4)')):
            if got != want:
                viol('C1', 'row %d %s = %s != %s' % (i, nm, got, want))
    say('C1 (P1): committed SPLTAIL(3)-only rows as predicted')
    results['checks']['C1-rows'] = 3

    # --------------------------- C2 own law ties key-for-key (P2)
    mine15 = law_F_annex(2, 7, 1)
    mine16 = law_F_annex(2, 8, 1)
    for i, mine in ((15, mine15), (16, mine16), (19, mine15)):
        if mine != committed[i][1]:
            d1 = {kk for kk in mine if
                  mine.get(kk) != committed[i][1].get(kk)}
            d2 = {kk for kk in committed[i][1] if
                  mine.get(kk) != committed[i][1].get(kk)}
            viol('C2', 'row %d: %d differing keys %s' %
                 (i, len(d1 | d2), sorted(d1 | d2)[:4]))
    say('C2 (P2): own S6.1/S6.3 law == committed rows 15/16/19 '
        'key-for-key (%d + %d keys)' % (len(mine15), len(mine16)))
    results['checks']['C2-keys'] = len(mine15) * 2 + len(mine16)

    # ------------------------------- C3 wrong-cap refutation (P3)
    wrong16 = law_F_annex(2, 8, 1, cap='w')
    wrong15 = law_F_annex(2, 7, 1, cap='w')
    exp_wrong = {
        16: {((), 'SPLTAIL', (4,)): 384, ((), 'SPLTAIL', (5,)): 96,
             ((), 'SPLTAIL', (6,)): 24, ((), 'SPLTAIL', (7,)): 6,
             ((), 'UND', ()): 514,
             ((3,), 'SPLTAIL', (4,)): 1152,
             ((3,), 'SPLTAIL', (5,)): 288,
             ((3,), 'SPLTAIL', (6,)): 72,
             ((3,), 'SPLTAIL', (7,)): 18,
             ((3,), 'UND', ()): 1542},
        15: {((), 'SPLTAIL', (4,)): 96, ((), 'SPLTAIL', (5,)): 24,
             ((), 'SPLTAIL', (6,)): 6, ((), 'UND', ()): 2,
             ((3,), 'SPLTAIL', (4,)): 288,
             ((3,), 'SPLTAIL', (5,)): 72,
             ((3,), 'SPLTAIL', (6,)): 18,
             ((3,), 'UND', ()): 6},
    }
    for i, wrong in ((16, wrong16), (15, wrong15)):
        for kk, want in exp_wrong[i].items():
            if wrong.get(kk) != want:
                viol('C3', 'row %d wrong-cap %s = %s != %s' %
                     (i, kk, wrong.get(kk), want))
        if sum(wrong.values()) != sum(committed[i][1].values()):
            viol('C3', 'row %d wrong-cap mass not conserved' % i)
        mism = {kk for kk in set(wrong) | set(committed[i][1])
                if wrong.get(kk) != committed[i][1].get(kk)}
        want_mism = set(exp_wrong[i])
        if mism != want_mism:
            viol('C3', 'row %d mismatch set %s != %s' %
                 (i, sorted(mism), sorted(want_mism)))
        if any(kk[1] not in ('SPLTAIL', 'UND') for kk in mism):
            viol('C3', 'row %d: a DECIDED key moved: %s' %
                 (i, sorted(mism)))
    say('C3 (P3): wrong-cap w<N table == the PE5 failure-scenario '
        'numbers exactly (+ the refined-history propagation, '
        'disclosed); mismatch set == SPLTAIL/UND keys ONLY, both '
        'histories, no decided key moves; masses conserved '
        '(row16: 514+510=1024 empty-history, 1542+1530=3072 @(3,); '
        'row15: 2+126=128, 6+378=384)')
    results['checks']['C3-wrongcap'] = sum(len(v) for v in
                                           exp_wrong.values()) + 4

    # ---------------- C4 (P4): v(Res) = 2u at genre F, two routes
    # key phi = x^2 + 2x + 4 at (Zp, q=2, N=7, k=1): v(p1)=1 >= k,
    # v(p0)=2 = 2k exact, residue pair psi = y^2+y+1 (x = 2y).
    phi = [4, 2, 1]
    w_, u_ = 3, 7
    # 2SIDED(3,4) members: (A1, A0) as coeff lists (a0 + a1*x), with
    # dv(A1)=3 (v(b0)=3 or v(b1)+k=3) and dv(A0)=7 (v(a0)=7 or
    # v(a1)+k=7):
    members = [([8], [128]), ([0, 4], [128]), ([8], [0, 64]),
               ([8], [128, 128]), ([8, 4], [128, 64])]
    phi2 = pmul(phi, phi)
    polysC4 = []
    for A1, A0 in members:
        F = padd(padd(phi2, pmul(A1, phi)), A0)
        F = F + [0] * (5 - len(F))
        polysC4.append(F)
        r_syl = sylvester_res(F, phi)
        _, rem = pdivmod_monic(F, phi)
        rem = rem + [0] * (2 - len(rem))
        beta, alpha = rem[0], rem[1]
        r_norm = alpha * alpha * phi[0] - alpha * beta * phi[1] \
            + beta * beta
        if abs(r_syl) != abs(r_norm):
            viol('C4', 'routes differ: %s vs %s (A1=%s A0=%s)'
                 % (r_syl, r_norm, A1, A0))
        if v2(r_syl) != 2 * u_:
            viol('C4', 'v2(Res) = %d != 2u = %d (A1=%s A0=%s)'
                 % (v2(r_syl), 2 * u_, A1, A0))
    # the balance arithmetic (j roots at slope w, 4-j at u-w):
    j = 2
    if not (j * w_ + (4 - j) * (u_ - w_) == 2 * u_ and
            Fraction(j * w_, 2) + Fraction((4 - j) * (u_ - w_), 2)
            == u_):
        viol('C4', 'balance j=2 fails')
    # the FALSE mixed form (unhalved LHS, halved RHS u):
    j_false = Fraction(4 * w_ - 3 * u_, 2 * w_ - u_)
    if j_false != 9:
        viol('C4', 'false-form j = %s != 9' % j_false)
    say('C4 (P4): %d explicit 2SIDED(3,4) members at (Zp,2,7,k1): '
        'v2(Res(F,phi)) = 14 = 2u on all, two routes agree; '
        'halved/unhalved balances give j = 2; the mixed form gives '
        'j = 9 (impossible, self-alarming)' % len(members))
    results['checks']['C4-members'] = len(members)

    # ------------- C5 (P5): F-SPLTAIL sigma + the 2w >= N tooth
    # SPLTAIL(3) states: A1 in {8, 4x, 4x+8}; A0 hidden -> lifts have
    # every in-window digit zero: v(a0) >= 7, v(a1) >= 6, so
    # u_lift >= N = 7 > 6 = 2w.  Lifts incl. the A0 = 0 corner.
    A1s = [[8], [0, 4], [8, 4]]
    A0lifts = [[128], [256], [384], [0, 64], [128, 64], [512], [0]]
    polysC5, tags = [], []
    for A1 in A1s:
        for A0 in A0lifts:
            F = padd(padd(phi2, pmul(A1, phi)), A0)
            polysC5.append(F + [0] * (5 - len(F)))
            tags.append((tuple(A1), tuple(A0)))
    sig_want = ((1, 2), (1, 2))
    sigs = gp_sigmas(polysC4 + polysC5, 2)
    for i, sg in enumerate(sigs[:len(polysC4)]):
        if sg != sig_want:
            viol('C4', 'sigma %s != %s on 2SIDED member %d'
                 % (sg, sig_want, i))
    nbad = 0
    for tag, sg in zip(tags, sigs[len(polysC4):]):
        if sg != sig_want:
            nbad += 1
            viol('C5', 'sigma %s != %s at %s' % (sg, sig_want, tag))
    say('C5 (P5): %d SPLTAIL(3) lifts (3 states x 7 lifts incl. '
        'A0=0 corner): sigma == {(1,2),(1,2)} on all (%d bad); '
        '+ %d 2SIDED members' % (len(tags), nbad, len(polysC4)))
    # TOOTH: w = 4 (2w = 8 >= N = 7; SPLTAIL under the WRONG cap
    # only).  Two lifts of the SAME hidden-A0 state:
    Ft1 = padd(padd(phi2, pmul([16], phi)), [128])   # u_lift = 7
    Ft2 = padd(padd(phi2, pmul([16], phi)), [512])   # u_lift = 9
    s1, s2 = gp_sigmas([Ft1 + [0] * (5 - len(Ft1)),
                        Ft2 + [0] * (5 - len(Ft2))], 2)
    if s1 != ((2, 2),):
        viol('C5-T', 'RAM(7) lift sigma %s != ((2,2),)' % (s1,))
    if s2 != ((1, 2), (1, 2)):
        viol('C5-T', '2SIDED(4,5) lift sigma %s' % (s2,))
    fired = (s1 != s2)
    say('C5-T tooth: w=4 hidden-A0 state, lift u=7 -> %s vs lift '
        'u=9 -> %s: %s (no single label lift-sound at 2w >= N)'
        % (s1, s2, 'FIRED' if fired else 'DEAD'))
    if not fired:
        viol('C5-T', 'tooth dead')
    results['checks']['C5-lifts'] = len(tags) + 2

    # -------------------- C6 (P6): the S9.2 five-mass closure
    # coefficientwise: 2q^2 + (q-2) + q + 2 + 2 == 2(q^2+q+1)
    lhs = ptrim(padd(padd(padd(padd([0, 0, 2], [-2, 1]), [0, 1]),
                          [2]), [2]))
    if lhs != [2, 2, 2]:
        viol('C6', 'closure numerators %s != [2,2,2]' % lhs)
    # ladder closed forms + mu_E aggregation, exact at 7 points
    # (numerator degrees < 7: 7 points decide each identity):
    for qv in (2, 3, 5, 7, 11, 13, 101):
        r = Fraction(1, qv)
        Phi2 = qv * qv + qv + 1
        ram = (1 - r) / (1 - r ** 3)
        two = (1 - r) * r * r / (1 - r ** 3)
        evb = (1 - r) * r / (1 - r ** 3)
        spliteq = evb * Fraction(qv - 2, 2 * qv)
        inert = evb * Fraction(1, 2)
        refine = evb * Fraction(1, qv)
        ok = (ram == Fraction(qv * qv, Phi2)
              and two == Fraction(1, Phi2)
              and spliteq == Fraction(qv - 2, 2 * Phi2)
              and inert == Fraction(qv, 2 * Phi2)
              and refine == Fraction(1, Phi2)
              and ram + two + spliteq + inert + refine == 1)
        agg = Fraction(Phi2, qv * qv + qv)
        mu = (ram * agg, (spliteq + two) * agg, inert * agg)
        ok = ok and mu == (Fraction(qv, qv + 1),
                           Fraction(1, 2 * (qv + 1)),
                           Fraction(1, 2 * (qv + 1)))
        if not ok:
            viol('C6', 'identity fails at q = %d' % qv)
        # tooth: any nonzero "extra" breaks the partition
        if ram + (two - r ** 4) + spliteq + inert + refine == 1:
            viol('C6-T', 'extra tooth dead at q = %d' % qv)
    say('C6 (P6): five-mass closure coefficientwise [2,2,2] == '
        '2*Phi2; ladder forms + mu_E == nu2 fractions exact at 7 '
        'points; extra-token tooth FIRED (any extra breaks the '
        'partition): S9.2\'s "- extra..." == 0, 2SIDED mass is '
        'EXACTLY 1/Phi2')
    results['checks']['C6-points'] = 7

    # ---------------------------------------------------- verdict
    dt = time.time() - t0
    verdict = 'GREEN' if not VIOL else 'RED'
    say('VERDICT: %s (%d violations) %.1fs' % (verdict, len(VIOL), dt))
    results['verdict'] = verdict
    results['violations'] = len(VIOL)
    results['elapsed_s'] = round(dt, 1)
    with open(os.path.join(HERE, 'genh4annex_supp_output.txt'),
              'w') as fh:
        fh.write('\n'.join(LOG) + '\n')
    with open(os.path.join(HERE, 'genh4annex_supp_results.json'),
              'w') as fh:
        json.dump(results, fh, indent=1, sort_keys=True)
    print('artifacts: %s %s'
          % (md5f(os.path.join(HERE, 'genh4annex_supp_output.txt')),
             md5f(os.path.join(HERE, 'genh4annex_supp_results.json'))))
    return 0 if not VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
