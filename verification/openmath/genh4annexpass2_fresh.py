#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""GENH4 ANNEX-PASS #2 FRESH ROUTE (hostile verifier leg, 2026-08-09).

Scoped to the post-R2 annex stack (ANNEX PE5 + ANNEX R + ANNEX R2 of
GENH4_PROOF_2026-08-08.md).  Route chosen to DIFFER from every prior
leg: the PE5 leg ran k = 1 rows; the R leg ran (2,11,2); annex-pass #1
FR1-FR5 ran (2,15,3), (3,11,2), the 54-cell grid, the (2,8,2)/(2,10,2)
counter-instances and (2,9,2).  All six cells below are fresh:
(2,7,2), (2,12,2), (3,13,2), (3,10,1), (2,14,2), (4,11,2).

FA -- ANNEX R2's corrected clause (c')(i): the u0 := least odd height
      >= max(N, 4k+1) witness pair at BAND-ZERO members, one cell per
      branch of the u0 trichotomy, mixed characteristic (PARI) plus
      an equal-characteristic (F_2[[t]]) differ-leg at the q = 2
      cells:
  FA1 cell (2,7,2), the N <= 4k branch (N = 7 < 4k+1 = 9; the A0
      slot string [4k+1, N+k-1] = [9,8] is EMPTY: the leaf is
      A0-hidden trivially, band empty).  w in {5, 6} (>= 2k+1 = 5
      per GENH4-1F's node), u0 = 4k+1 = 9 <= 2w-1.
      PREREGISTERED: every b0@9 lift and the b1@7-route lift (u = 9
      odd <= 2w) reads PARI sigma = {(2,2)} (S7 F-RAM); every
      b0@(2w+1) lift (u = 2w+1 > 2w) reads {(1,2),(1,2)} (S7
      F-2SIDED); equal-char (F_2[[t]]): RAM witnesses have disc != 0
      and 0 roots in F_4[[t]]; 2SIDED witnesses have exactly 4 roots
      in F_4[[t]] and 0 in F_2[[t]] -- sigma DIFFERS in BOTH
      characteristics.
  FA2 cell (2,12,2), the N even >= 4k+2 branch: w = 7, u0 = N+1 =
      13 <= 2w = 14.  PREREGISTERED: band-zero b0@13 -> {(2,2)};
      band-zero b0@15 (u = 15 > 14) -> {(1,2),(1,2)}; band-pinned
      (b1@11, m = 13) with b0 = 0 -> u = 13 = m odd <= 2w ->
      {(2,2)} (the S7 RAM leg is stratum-blind); the same equal-char
      differ-leg on the band-zero pair.
  FA3 cell (3,13,2), the N odd >= 4k+1 branch: w = 7, u0 = N = 13.
      PREREGISTERED: band-zero b0@13 -> {(2,2)}; b0@15 ->
      {(1,2),(1,2)}.
FB -- ANNEX R2's (c')(ii) at 2w = N: DIRECT PARI verification of the
      inert-continuation existence, both residue characteristics --
      the FIRST machine exercise of the 2w = N leg anywhere (pass #1
      FR5 was N odd; the 2w = N leg was paper-only):
  FB1 cell (3,10,1), char odd: 8 members (pin letter S1 = d0' +
      d1*ybar sweeping F_9^x, psi = y^2 + y + 2) x lifts {b0 =
      d0*3^10, d0 in {1,2}} (u = 10 = 2w residual read) + {b0 =
      3^11} (u = 11 > 2w).  PREREGISTERED: the in-script F_9
      residual computation (disc = S1^2 - 4*d0 = S1^2 - d0; nonzero
      square -> '11' -> {(1,2),(1,2)}; non-square -> '2' -> {(1,4)};
      zero -> '1sq', recorded NOT gated) matches PARI
      member-for-member on every decided read; at least ONE (S1, d0)
      is INERT (R2.M2's completed coset count, machine-witnessed);
      the SAME member's u = 11 lift reads {(1,2),(1,2)}: the
      (c')(ii) differing pair at one member.  Numeric premise:
      |Sq(F_9)| = 4 and |Sq u {0}| = 5, neither divisible by q = 3
      (the M2 count).
  FB2 cell (2,14,2), residue char 2 (Z_2): w = 7, pins S1 in {ybar,
      1, ybar+1} of F_4 (psi = y^2 + y + 1).  PREREGISTERED (the
      trace argument, R2.REM Remark 2): the d0 = 1 lift (u = 14 =
      2w) reads INERT {(1,4)} iff Tr_{F_4/F_2}(1/S1^2) = 1 iff
      S1 != 1 -- pins ybar and ybar+1 -> {(1,4)}, pin 1
      (tau-degenerate) -> '11' -> {(1,2),(1,2)}; every member's
      b0@15 lift (u = 15 > 2w) -> {(1,2),(1,2)}; the A0 = 0 lift ->
      {(1,2),(1,2)} (F = phi*(phi + A1), both factors genre-F).
FC -- NON-PRIME q: the CONSUMED clause GENH4-7'(b) at q = 4 (never
      exercised at any non-prime q anywhere in the GENH4 arc): cell
      (4,11,2) over W(F_4)-of-fraction-field K = Q(y)/(y^2 + y + 1)
      (2 is INERT in K, residue field F_4), phi = x^2 + 4x + 16y
      (v(p1) = 2 >= k, v(p0) = 4 = 2k exact, residue pair psi =
      t^2 + t + w irreducible over F_4 since Tr_{F_4/F_2}(w) = 1).
      SPLTAIL(5): 2w = 10 < N = 11.  3 pins (height-5 letters ybar,
      1, ybar + w) x 3 band values (height 12 = the k-1 = 1 band
      slot: 0, 2^10, 2^10 y) x 4 lifts (A0 = 0 corner; b0@11 = the
      u = N lift; b0 = 2^13 y; band-route lb1@11 + b0@14).
      PREREGISTERED: all 36 members read RELATIVE sigma over K_v
      = {(1,2),(1,2)} (from the absolute polynomial's
      idealprimedec at 2: every absolute f is even because 2 is
      inert in K; rel pair = (e, f/2)); the valuation layer u >= N,
      and u <= m = 12 at band-nonzero members, holds on every
      member; TEETH: b0@9 (u = 9 odd <= 2w, with and without a band
      digit) flips to relative {(2,2)} -- must FIRE 2/2.

Exit 0 iff zero violations.  Artifacts:
genh4annexpass2_fresh_output.txt, genh4annexpass2_fresh_results.json.
"""
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
LOG = []
VIOL = []


def say(s):
    print(s)
    LOG.append(s)


def viol(tag, msg):
    VIOL.append((tag, msg))
    say('VIOLATION [%s] %s' % (tag, msg))


SIG_2S = ((1, 2), (1, 2))
SIG_RAM = ((2, 2),)
SIG_IN = ((1, 4),)


# ---- integer x-polynomial helpers (committed fresh-leg conventions)
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


def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def quartic(phi, a1, a0, b1, b0):
    """F = phi^2 + (a1 x + a0) phi + (b1 x + b0), padded to deg 4."""
    F = padd(padd(pmul(phi, phi), pmul([a0, a1], phi)), [b0, b1])
    return F + [0] * (5 - len(F))


def gp_run(script):
    gp = os.path.expanduser('~/.local/bin/gp')
    if not os.path.exists(gp):
        gp = 'gp'
    r = subprocess.run([gp, '-q'], input=script.encode(),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       timeout=1800)
    if r.returncode != 0:
        raise RuntimeError('gp failed: %s' % r.stderr.decode()[:400])
    return r.stdout.decode()


GP_SIG = r"""
ef(g, p) = {
  if (poldegree(g) == 1, return([1, 1]));
  my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));
  [dec[1].e, dec[1].f]
}
sig(f, p) = {
  my(d = poldisc(f), F);
  if (d == 0, return([[-1, -1]]));
  F = factorpadic(f, p, 300);
  vecsort(vector(matsize(F)[1], i, ef(liftall(F[i, 1]), p)))
}
"""


def parse_sigs(out, n):
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            nums = [int(x) for x in rest.replace('[', ' ')
                    .replace(']', ' ').replace(',', ' ').split()]
            got[int(idx)] = tuple(sorted(zip(nums[0::2], nums[1::2])))
    return [got[i] for i in range(n)]


def gp_sigmas(polys, p):
    lines = [GP_SIG]
    for i, cs in enumerate(polys):
        expr = '+'.join('(%d)*x^%d' % (c, j) for j, c in enumerate(cs))
        lines.append('print("R %d ", sig(%s, %d))' % (i, expr, p))
    lines.append('quit')
    return parse_sigs(gp_run('\n'.join(lines)), len(polys))


# -------- F_9 arithmetic (psi = y^2 + y + 2: ybar^2 = 2 ybar + 1
# over F_3); element = (a, b) meaning a + b*ybar
def f9mul(u, v):
    a, b = u
    c, d = v
    return ((a * c + b * d) % 3, (a * d + b * c + 2 * b * d) % 3)


def main():
    t0 = time.time()
    results = {'checks': {}}
    import genh4annexr_supp as RS   # F4MUL/count_roots/fp_disc_nonzero

    # ============ FA1: (2,7,2), the N <= 4k branch of (c')(i)
    phi2 = [16, 4, 1]
    polys, metas = [], []
    for w, pins in ((5, ((8, 0), (0, 32), (8, 32))),
                    (6, ((16, 0), (0, 64), (16, 64)))):
        for pi, (a1, a0) in enumerate(pins):
            for tag, (b1, b0), exp in (
                    ('u9', (0, 1 << 9), SIG_RAM),
                    ('u9b1', (1 << 7, 0), SIG_RAM),
                    ('u2w1', (0, 1 << (2 * w + 1)), SIG_2S)):
                u = min((vp(b1, 2) + 2) if b1 else 10 ** 9,
                        vp(b0, 2) if b0 else 10 ** 9)
                if u < 9:
                    viol('FA1', 'u=%d < max(N,4k+1)=9 (%s)' % (u, tag))
                polys.append(quartic(phi2, a1, a0, b1, b0))
                metas.append(('w%d-p%d-%s' % (w, pi, tag), exp))
    sigs = gp_sigmas(polys, 2)
    bad = 0
    for (tag, exp), sg in zip(metas, sigs):
        if sg != exp:
            bad += 1
            viol('FA1', '%s: sigma %s != %s' % (tag, sg, exp))
    say('FA1 (2,7,2) N<=4k branch: u0=9 RAM witnesses (incl. the '
        'b1@7 route) + u=2w+1 2SIDED witnesses, band-zero (A0 slot '
        'string EMPTY): %d/%d PARI match'
        % (len(polys) - bad, len(polys)))
    results['checks']['FA1'] = len(polys) - bad

    # ---- equal-characteristic differ-leg (F_2[[t]]) for FA1 + FA2
    def tpoly(pairs):
        out = []
        for exps in pairs:
            s = [0] * RS.PREC
            for e in exps:
                s[e] ^= 1
            out.append(s)
        return out

    def txmul(A, B):
        r = [[0] * RS.PREC for _ in range(len(A) + len(B) - 1)]
        for i, ax in enumerate(A):
            for j, bx in enumerate(B):
                conv = [0] * RS.PREC
                for ii, av in enumerate(ax):
                    if av:
                        for jj, bv in enumerate(bx):
                            if bv and ii + jj < RS.PREC:
                                conv[ii + jj] ^= 1
                r[i + j] = RS.sadd(r[i + j], conv)
        return r

    def txadd(A, B):
        n = max(len(A), len(B))
        z = [0] * RS.PREC
        return [RS.sadd(A[i] if i < len(A) else z,
                        B[i] if i < len(B) else z) for i in range(n)]

    phit = tpoly([[4], [2], [0]])           # x^2 + t^2 x + t^4
    eqlegs = (
        ('FA1eq-RAM', tpoly([[], [3]]), tpoly([[9]]), 'RAM'),
        ('FA1eq-2S', tpoly([[], [3]]), tpoly([[11]]), '2S'),
        ('FA2eq-RAM', tpoly([[], [5]]), tpoly([[13]]), 'RAM'),
        ('FA2eq-2S', tpoly([[], [5]]), tpoly([[15]]), '2S'))
    neq = 0
    for tag, A1t, A0t, kind in eqlegs:
        Ft = txadd(txadd(txmul(phit, phit), txmul(A1t, phit)), A0t)
        if not RS.fp_disc_nonzero([list(c) for c in Ft]):
            viol('FAeq', '%s: disc == 0 in F_2(t)' % tag)
            continue
        r4 = RS.count_roots([list(c) for c in Ft], (0, 1, 2, 3))
        r2 = RS.count_roots([list(c) for c in Ft], (0, 1))
        ok = (r4 == 0) if kind == 'RAM' else (r4 == 4 and r2 == 0)
        if not ok:
            viol('FAeq', '%s: roots (r4=%d, r2=%d)' % (tag, r4, r2))
        else:
            neq += 1
    say('FA equal-char differ-leg (F_2[[t]]): %d/4 -- RAM witnesses '
        '0 roots in F_4[[t]] (disc != 0); 2SIDED witnesses 4 roots '
        'in F_4[[t]], 0 in F_2[[t]]: the (c\')(i) pair differs in '
        'BOTH characteristics at (2,7,2) and (2,12,2)' % neq)
    results['checks']['FAeq'] = neq

    # ============ FA2: (2,12,2), the N even >= 4k+2 branch
    polys, metas = [], []
    for pi, (a1, a0) in enumerate(((32, 0), (0, 128), (32, 128))):
        for tag, (b1, b0), exp in (
                ('bz-u13', (0, 1 << 13), SIG_RAM),
                ('bz-u15', (0, 1 << 15), SIG_2S),
                ('bp-u13', (1 << 11, 0), SIG_RAM)):
            u = min((vp(b1, 2) + 2) if b1 else 10 ** 9,
                    vp(b0, 2) if b0 else 10 ** 9)
            if u < 12:
                viol('FA2', 'u=%d < N=12 (%s)' % (u, tag))
            polys.append(quartic(phi2, a1, a0, b1, b0))
            metas.append(('p%d-%s' % (pi, tag), exp))
    sigs = gp_sigmas(polys, 2)
    bad = 0
    for (tag, exp), sg in zip(metas, sigs):
        if sg != exp:
            bad += 1
            viol('FA2', '%s: sigma %s != %s' % (tag, sg, exp))
    say('FA2 (2,12,2) N-even branch: u0=13 RAM + u=15 2SIDED at '
        'band-zero, u=13=m RAM at band-pinned: %d/%d PARI match'
        % (len(polys) - bad, len(polys)))
    results['checks']['FA2'] = len(polys) - bad

    # ============ FA3: (3,13,2), the N odd >= 4k+1 branch
    phi3 = [162, 9, 1]
    polys, metas = [], []
    for pi, (a1, a0) in enumerate(((243, 0), (0, 2187), (243, 2187),
                                   (486, 2187))):
        for tag, b0, exp in (('u13', 3 ** 13, SIG_RAM),
                             ('u15', 3 ** 15, SIG_2S)):
            polys.append(quartic(phi3, a1, a0, 0, b0))
            metas.append(('p%d-%s' % (pi, tag), exp))
    sigs = gp_sigmas(polys, 3)
    bad = 0
    for (tag, exp), sg in zip(metas, sigs):
        if sg != exp:
            bad += 1
            viol('FA3', '%s: sigma %s != %s' % (tag, sg, exp))
    say('FA3 (3,13,2) N-odd branch: u0=N=13 RAM + u=15 2SIDED at '
        'band-zero: %d/%d PARI match' % (len(polys) - bad, len(polys)))
    results['checks']['FA3'] = len(polys) - bad

    # ============ FB1: (3,10,1), 2w = N = 10, char odd
    phi31 = [18, 3, 1]
    els9 = [(a, b) for a in range(3) for b in range(3)
            if (a, b) != (0, 0)]
    Sq = set(f9mul(e, e) for e in els9)
    if len(Sq) != 4 or len(Sq) % 3 == 0 or (len(Sq) + 1) % 3 == 0:
        viol('FB1', 'coset-count premise: |Sq| = %d' % len(Sq))
    polys, metas = [], []
    n_inert_pred = 0
    for d0p, d1 in els9:
        S1 = (d0p, d1)
        a1, a0 = d1 * 3 ** 4, d0p * 3 ** 5
        S1sq = f9mul(S1, S1)
        for d0 in (1, 2):
            disc = ((S1sq[0] - d0) % 3, S1sq[1])
            if disc == (0, 0):
                pred, kind = None, '1sq'
            elif disc in Sq:
                pred, kind = SIG_2S, '11'
            else:
                pred, kind = SIG_IN, '2'
                n_inert_pred += 1
            polys.append(quartic(phi31, a1, a0, 0, d0 * 3 ** 10))
            metas.append(('S1=%d+%dy,d0=%d' % (d0p, d1, d0), pred,
                          kind))
        polys.append(quartic(phi31, a1, a0, 0, 3 ** 11))
        metas.append(('S1=%d+%dy,u11' % (d0p, d1), SIG_2S, 'u>2w'))
    sigs = gp_sigmas(polys, 3)
    bad = ndec = 0
    inert_confirmed = []
    for (tag, pred, kind), sg in zip(metas, sigs):
        if pred is None:
            say('FB1 note: %s residual 1sq (recorded, ungated): '
                'sigma %s' % (tag, sg))
            continue
        ndec += 1
        if sg != pred:
            bad += 1
            viol('FB1', '%s [%s]: sigma %s != %s' % (tag, kind, sg,
                                                     pred))
        elif kind == '2':
            inert_confirmed.append(tag)
    if not inert_confirmed:
        viol('FB1', 'NO inert continuation at 2w = N: (c\')(ii)/'
             'R2.M2 existence FAILS at (3,10,1)')
    say('FB1 (3,10,1) 2w=N char-odd: %d decided reads, %d/%d PARI '
        'match member-for-member; INERT continuations EXIST (%d '
        'members, first %s -> {(1,4)}), each member also carrying '
        'the u=11 lift {(1,2),(1,2)}: the (c\')(ii) differing pair '
        'machine-witnessed; %d inert reads predicted by the F_9 '
        'residual computation'
        % (ndec, ndec - bad, ndec, len(inert_confirmed),
           inert_confirmed[0] if inert_confirmed else '-',
           n_inert_pred))
    results['checks']['FB1-inert'] = len(inert_confirmed)

    # ============ FB2: (2,14,2), 2w = N = 14, residue char 2
    polys, metas = [], []
    for a1, a0, s1n, tau0 in ((32, 0, 'ybar', False),
                              (0, 128, '1', True),
                              (32, 128, 'ybar+1', False)):
        exp14 = SIG_2S if tau0 else SIG_IN
        for tag, b0, exp in (('u14', 1 << 14, exp14),
                             ('u15', 1 << 15, SIG_2S),
                             ('A0=0', 0, SIG_2S)):
            polys.append(quartic(phi2, a1, a0, 0, b0))
            metas.append(('S1=%s-%s' % (s1n, tag), exp))
    sigs = gp_sigmas(polys, 2)
    bad = 0
    for (tag, exp), sg in zip(metas, sigs):
        if sg != exp:
            bad += 1
            viol('FB2', '%s: sigma %s != %s' % (tag, sg, exp))
    say('FB2 (2,14,2) 2w=N residue-char-2: trace-leg predictions '
        '(S1 in {ybar, ybar+1}: u=14 INERT {(1,4)}; S1 = 1 '
        'tau-degenerate: {(1,2),(1,2)}; u=15 and A0=0 lifts '
        '{(1,2),(1,2)}): %d/%d PARI match -- FIRST machine exercise '
        'of the 2w=N leg; the (c\')(ii) pair exists at the tau != 0 '
        'members' % (len(polys) - bad, len(polys)))
    results['checks']['FB2'] = len(polys) - bad

    # ============ FC: (4,11,2) over W(F_4) -- non-prime q
    # x-poly coefficients are (a, b) = a + b*y in Z[y], y^2 = -y - 1
    def ymul(u, v):
        a, b = u
        c, d = v
        return (a * c - b * d, a * d + b * c - b * d)

    def yadd(u, v):
        return (u[0] + v[0], u[1] + v[1])

    def yxmul(A, B):
        r = [(0, 0)] * (len(A) + len(B) - 1)
        for i, ax in enumerate(A):
            for j, bx in enumerate(B):
                r[i + j] = yadd(r[i + j], ymul(ax, bx))
        return r

    def yxadd(A, B):
        n = max(len(A), len(B))
        return [yadd(A[i] if i < len(A) else (0, 0),
                     B[i] if i < len(B) else (0, 0))
                for i in range(n)]

    def yv2(c):
        vs = [vp(z, 2) for z in c if z]
        return min(vs) if vs else None

    phiY = [(0, 16), (4, 0), (1, 0)]        # x^2 + 4x + 16y
    pinsY = ([(0, 0), (8, 0)],              # a1 = 8: letter ybar
             [(32, 0), (0, 0)],             # a0 = 32: letter 1
             [(0, 32), (8, 0)])             # letter ybar + w
    bandsY = ((None, (0, 0)), (12, (1 << 10, 0)), (12, (0, 1 << 10)))
    liftsY = (('A0=0', (0, 0), (0, 0)),
              ('u11', (0, 0), (1 << 11, 0)),
              ('u13', (0, 0), (0, 1 << 13)),
              ('u13b', (1 << 11, 0), (1 << 14, 0)))
    members, mmeta = [], []
    for pi, A1 in enumerate(pinsY):
        for bi, (mband, bb1) in enumerate(bandsY):
            for tag, lb1, b0 in liftsY:
                b1 = yadd(bb1, lb1)
                F = yxadd(yxadd(yxmul(phiY, phiY), yxmul(A1, phiY)),
                          [b0, b1])
                v0, v1 = yv2(b0), yv2(b1)
                u = min(v0 if v0 is not None else 10 ** 9,
                        (v1 + 2) if v1 is not None else 10 ** 9)
                if u < 10 ** 9 and u < 11:
                    viol('FC', 'p%db%d-%s: u=%d < N=11'
                         % (pi, bi, tag, u))
                if mband is not None and u > mband:
                    viol('FC', 'p%db%d-%s: u=%d > m=%d'
                         % (pi, bi, tag, u, mband))
                members.append(F)
                mmeta.append('p%db%d-%s' % (pi, bi, tag))
    teeth, tmeta = [], []
    for tag, bb1 in (('tooth-u9', (0, 0)), ('tooth-u9b', (1 << 10, 0))):
        F = yxadd(yxadd(yxmul(phiY, phiY),
                        yxmul([(0, 0), (8, 0)], phiY)),
                  [(1 << 9, 0), bb1])
        teeth.append(F)
        tmeta.append(tag)

    def gp_ypoly(F):
        return '+'.join('(%d+(%d)*y)*x^%d' % (c[0], c[1], j)
                        for j, c in enumerate(F))

    lines = [r"""
K = nfinit(y^2+y+1);
relsig(F) = {
  my(d = poldisc(F), fa, g, ab, nf2, dec, out = List());
  if (d == 0, return([[-1, -1]]));
  fa = nffactor(K, F);
  for (i = 1, matsize(fa)[1],
    g = fa[i, 1];
    if (poldegree(g) == 1, listput(out, [1, 1]),
      ab = rnfequation(K.pol, g);
      nf2 = nfinit([ab, [2]]);
      dec = idealprimedec(nf2, 2);
      for (j = 1, #dec,
        listput(out, [dec[j].e, dec[j].f / 2]))));
  vecsort(Vec(out))
}
"""]
    for i, F in enumerate(members + teeth):
        lines.append('print("R %d ", relsig(%s))' % (i, gp_ypoly(F)))
    lines.append('quit')
    sigsY = parse_sigs(gp_run('\n'.join(lines)),
                       len(members) + len(teeth))
    bad = 0
    for tag, sg in zip(mmeta, sigsY[:len(members)]):
        if sg != SIG_2S:
            bad += 1
            viol('FC', '%s: rel sigma %s != {(1,2),(1,2)}' % (tag, sg))
    fired = 0
    for tag, sg in zip(tmeta, sigsY[len(members):]):
        if sg != SIG_RAM:
            viol('FC', '%s: rel sigma %s != {(2,2)}' % (tag, sg))
        if sg != SIG_2S:
            fired += 1
    say('FC (4,11,2) over W(F_4) -- FIRST non-prime-q exercise of '
        'the consumed clause GENH4-7\'(b): %d/%d members (3 pins x '
        '3 band values x 4 lifts incl. A0=0 corner and u=N) read '
        'relative sigma {(1,2),(1,2)} over K_v; u>=N and u<=m '
        'verified on the valuation layer; wrong-floor teeth FIRED '
        '%d/2 (rel {(2,2)})' % (len(members) - bad, len(members),
                                fired))
    results['checks']['FC'] = len(members) - bad
    results['checks']['FC-teeth'] = fired

    # ---------------------------------------------------- verdict
    dt = time.time() - t0
    verdict = 'GREEN' if not VIOL else 'RED'
    say('VERDICT: %s (%d violations) %.1fs' % (verdict, len(VIOL), dt))
    results['verdict'] = verdict
    results['violations'] = len(VIOL)
    results['elapsed_s'] = round(dt, 1)
    with open(os.path.join(HERE,
                           'genh4annexpass2_fresh_output.txt'),
              'w') as fh:
        fh.write('\n'.join(LOG) + '\n')
    with open(os.path.join(HERE,
                           'genh4annexpass2_fresh_results.json'),
              'w') as fh:
        json.dump(results, fh, indent=1, sort_keys=True, default=repr)
    return 0 if not VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
