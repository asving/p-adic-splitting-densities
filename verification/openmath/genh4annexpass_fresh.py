#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""GENH4 ANNEX-PASS FRESH ROUTE (hostile verifier leg, 2026-08-09).

Scoped to the two GENH4 annexes (ANNEX PE5 + ANNEX R).  Route chosen
to DIFFER from both annex machine legs: the annex R leg ran the single
cell (q,N,k) = (2,11,2) and the PE5 leg ran k = 1 rows only.  Here:

FR1 (first k = 3 cell EVER): fresh independent typing of the genre-F
    S6.1/S6.3 law at (2,15,3) — first-live check (no SPLTAIL at
    N = 13, 14; SPLTAIL(7) only at N = 15 = 4k+3), SPLTAIL(7) =
    3 * 2^17 * 4 with deep0 = 4 = q^{k-1} (band width k-1 = 2:
    heights 16, 17), node mass 2^26 exact, and the SEALED runner's
    law_F(2,15,3) tied KEY-FOR-KEY (first k = 3 exercise of the
    sealed law anywhere).
FR2 (char-0 sigma at two fresh cells, PARI):
    cell A (2,15,3) SPLTAIL(7), key phi = x^2 + 8x + 64 (v(p1) = 3
    >= k, v(p0) = 6 = 2k exact, psi = y^2+y+1): 48 members = 3 pin
    letters x 4 band values (TWO free band digits b1@13, b1@14 —
    the first multi-digit band anywhere) x 4 lifts (incl. A0 = 0
    corner and u_lift = N = 15), all sigma = {(1,2),(1,2)};
    cell B (3,11,2) SPLTAIL(5), key phi = x^2 + 9x + 162 (psi =
    y^2+y+2 irred over F_3): 48 members = 4 pins x 3 band values
    (b1@10, digit in F_3 — first odd-q k >= 2 exercise) x 4 lifts,
    all sigma = {(1,2),(1,2)}.  GENH4-7'(a)'s two inequalities
    checked on every member at the valuation layer: u_lift >= N
    always, and u_lift <= m (lowest nonzero band height) at every
    band-nonzero member.
    TEETH: wrong-floor mutants at both cells (b0@13 resp. b0@9:
    u odd <= 2w -> RAM) must flip sigma to {(2,2)}.
FR3 (the deep0 = q^{k-1} identity, symbolic + grid): the A0 slot
    string 4k+1..N+k-1 carries EXACTLY k-1 slots above N (heights
    N+1..N+k-1, comp 1 each) for every N >= 4k, so S6.3's deep0
    factor is q^{k-1} identically on the SPLTAIL-live range (first
    live N >= 4k+3); checked as a slot-count identity on the grid
    q in {2,3,5}, k in {1,2,3}, N in 4k+1..4k+6, PLUS the full
    fresh-vs-sealed law tie at every grid cell, PLUS the first-live
    boundary (SPLTAIL nonempty iff N >= 4k+3).
FR4 (VERIFIER COUNTER-INSTANCES to ANNEX R's R2 N-even band-pinned
    leg -- two cells):
    Cell (2,8,2) (N <= 4k): UND key (2w = 12 >= N = 8), band-pinned
    stratum m = N+1 = 9 (b1@7 != 0), w = 6: the u = N = 8 read that
    R2's "Lift 2" invokes is STRUCTURALLY UNREALIZABLE -- the
    height-8 letter's two components sit BELOW the entry budget
    floors (b0@8 < v(beta0) >= 4k+1 = 9; b1@6 < v(beta1) >= 3k+1
    = 7), so every lift has u = 9 = m -> RAM(9) -> sigma = {(2,2)}
    CONSTANT across the stratum, both characteristics: R2's
    within-stratum differing pair does not exist there.  (First
    detected by this leg's own smoke: u = 8 "lifts" built in
    violation of the budget floor came back OUTSIDE the F
    dictionary entirely -- {(2,1),(2,1)}/disc 0 -- they are not
    lifts of family members; disclosed, construction corrected.)
    Cell (2,10,2) (N >= 4k+2, the refine-path adjudication): w = 7,
    band-pinned m = 11 (b1@9 != 0), dmu = 5 < w: the u = 10 lift
    (b0@10, IN budget) reads '1sq' at depth 5 (S1-slot 0, char 2)
    and refines; ANNEX R2's refine-deeper display predicts the
    fresh 2SIDED'(6,7) -> sigma = {(1,2),(1,2)} "for every such
    lift"; the VERIFIER's derivation predicts RAM(11) -> {(2,2)}
    (the fresh leaf dv(A0') = 2*dmu+3 = 13 is unrealizable: the
    height-11 band letter's ybar-component d1 != 0 survives the
    refine's correction terms -- lambda's contributions land at
    heights >= 12 -- so dv(A0') = 11 odd <= 2w is FORCED).  PARI
    adjudicates between the two displayed predictions.  All other
    lifts (u = 11) predicted {(2,2)} by both.  PLUS band-ZERO
    contrast members of the SAME keys (u = 13 resp. 15 > 2w)
    predicted {(1,2),(1,2)}: the KEY-level differing pair that
    keeps clause (c)'s conclusion alive cross-stratum.
FR5 (the Codex-cell repaired witness, R2's N-odd leg): at
    (2,9,2), w = 5, band-pinned m = 10 = 2w (Codex's F4 instance):
    lift b0@9 -> RAM(9) -> {(2,2)} vs lift u = 10 (b0 = 0 or
    b0@10) -> the separable dmu1 = 5 = w read -> decided
    {(1,2),(1,2)} or {(1,4)}: the differing pair EXISTS exactly as
    R2 displays.  3 pins x 3 lifts.

DISCLOSURE: FR1-FR3 ran GREEN on the first launch; the two cell-A
teeth in that launch were buggy IN THIS SCRIPT (A0 built as x^13
instead of the coefficient pair -- degree-13 polynomial, PARI sigma
of the wrong object); fixed here.  FR4/FR5 were added after the
verifier's hand derivation of the counter-instance, BEFORE any
FR4/FR5 machine output existed; predictions above are preregistered
in this docstring.

Exit 0 iff zero violations.  Artifacts: genh4annexpass_fresh_output.txt,
genh4annexpass_fresh_results.json.
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


SIG_SPLTAIL = ((1, 2), (1, 2))
SIG_RAM_F = ((2, 2),)


# ==== my OWN typing of the genre-F law (S6.1 strings + S6.3 exits) ==
def my_law_F(q, N, k):
    A1all = list(range(2 * k + 1, N + k))
    A0all = list(range(4 * k + 1, N + k))
    comp = lambda m: 2 if m <= N - 1 else 1
    Q = q * q
    out = {}

    def put(kk, v):
        if v:
            out[kk] = out.get(kk, 0) + v

    def rec(f1, f0, wt, H2):
        A1 = [s for s in A1all if s > f1]
        A0 = [s for s in A0all if s > f0]
        band = q ** sum(comp(s) for s in A0 if s > N)
        for w in A1:
            if 2 * w < N:
                put((H2, 'SPLTAIL', (w,)), wt * (q ** comp(w) - 1)
                    * q ** sum(comp(s) for s in A1 if s > w) * band)
        put((H2, 'UND', ()), wt * band
            * q ** sum(comp(s) for s in A1 if 2 * s >= N))
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
                    put((H2, 'SPLITEQ', (dmu,)),
                        wt * on1 * nz0 * (Q - 1) * (Q - 2) // 2)
                    put((H2, 'INERT', (dmu,)),
                        wt * on1 * nz0 * Q * (Q - 1) // 2)
                    rec(dmu, u, wt * (Q - 1), H2 + (dmu,))

    rec(2 * k, 4 * k, 1, ())
    return out


# =============================== polynomial + valuation helpers =====
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
  F = factorpadic(f, p, 300);
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
                       timeout=1800)
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


def build_cell(p, k, N, phi, pins, bands, lifts):
    """Members: F = phi^2 + A1*phi + A0.  pins/bands/lifts are lists
    of (a1, a0, b1, b0) integer quadruples ADDED together; returns
    (polys, metas): meta = (tag, u_lift, m_band)."""
    polys, metas = [], []
    for pi, (pa1, pa0) in enumerate(pins):
        for bi, (bb1, m_band) in enumerate(bands):
            for li, (la1, la0, lb1, lb0) in enumerate(lifts):
                a1, a0 = pa1 + la1, pa0 + la0
                b1, b0 = bb1 + lb1, lb0
                A1 = [a0, a1]
                A0 = [b0, b1]
                F = padd(padd(pmul(phi, phi), pmul(A1, phi)), A0)
                F = F + [0] * (5 - len(F))
                if b0 == 0 and b1 == 0:
                    u = None
                else:
                    vb0 = vp(b0, p)
                    vb1 = vp(b1, p)
                    u = min(vb0 if vb0 is not None else 10 ** 9,
                            (vb1 + k) if vb1 is not None else 10 ** 9)
                polys.append(F)
                metas.append(('p%db%dL%d' % (pi, bi, li), u, m_band))
    return polys, metas


def main():
    t0 = time.time()
    results = {'checks': {}}
    import genh4_checks as GC

    # ---------------------------------------- FR1: the k = 3 cell
    for N in (13, 14):
        spl = [kk for kk in my_law_F(2, N, 3) if kk[1] == 'SPLTAIL']
        if spl:
            viol('FR1', '(2,%d,3) SPLTAIL %s (expected none)' % (N, spl))
    mine = my_law_F(2, 15, 3)
    spl = [kk for kk in mine if kk[1] == 'SPLTAIL']
    if spl != [((), 'SPLTAIL', (7,))]:
        viol('FR1', '(2,15,3) SPLTAIL keys %s' % spl)
    v = mine.get(((), 'SPLTAIL', (7,)))
    if v != 3 * 2 ** 17 * 4 or v != 1572864:
        viol('FR1', 'SPLTAIL(7) = %s != 3*2^17*4' % v)
    if sum(mine.values()) != 2 ** 26:
        viol('FR1', 'node mass %d != 2^26' % sum(mine.values()))
    sealed = GC.law_F(2, 15, 3)
    if sealed != mine:
        d = {kk for kk in set(sealed) | set(mine)
             if sealed.get(kk) != mine.get(kk)}
        viol('FR1', 'sealed law_F(2,15,3) differs on %d keys %s'
             % (len(d), sorted(d)[:4]))
    say('FR1: k=3 first live at N=15=4k+3 (none at 13/14); '
        'SPLTAIL(7) = %d = 3*2^17*4, deep0 = 4 = q^(k-1) (band '
        'heights 16,17); node mass 2^26 exact; SEALED law_F(2,15,3) '
        'ties my fresh typing key-for-key (%d keys) -- first k=3 '
        'exercise of the sealed law' % (v, len(sealed)))
    results['checks']['FR1-keys'] = len(sealed)

    # ------------------------- FR2 cell A: (2,15,3) SPLTAIL(7)
    phiA = [64, 8, 1]
    pinsA = [(16, 0), (0, 128), (16, 128)]          # letter at height 7
    bandsA = [((c13 << 13) | (c14 << 14),
               (16 if c13 else (17 if c14 else None)))
              for c13 in (0, 1) for c14 in (0, 1)]
    liftsA = [(0, 0, 0, 0),
              (0, 0, 0, 1 << 15),                    # u = 15 = N
              (0, 0, 0, 1 << 17),
              (0, 1 << 16, 1 << 15, 1 << 19)]
    polysA, metasA = build_cell(2, 3, 15, phiA, pinsA, bandsA, liftsA)
    for tag, u, m in metasA:
        if u is not None and u < 15:
            viol('FR2A', '%s u_lift = %s < N = 15' % (tag, u))
        if m is not None and u is not None and u > m:
            viol('FR2A', '%s u_lift = %s > band m = %s' % (tag, u, m))
    sigsA = gp_sigmas(polysA, 2)
    badA = sum(1 for sg in sigsA if sg != SIG_SPLTAIL)
    for (tag, u, m), sg in zip(metasA, sigsA):
        if sg != SIG_SPLTAIL:
            viol('FR2A', '%s (u=%s m=%s): sigma %s' % (tag, u, m, sg))
    say('FR2A: (2,15,3) SPLTAIL(7): %d members (3 pins x 4 band '
        'values [2 FREE band digits] x 4 lifts incl. A0=0 corner + '
        'u=N=15): PARI sigma == {(1,2),(1,2)} on all (%d bad); '
        'u>=15 and u<=m at band-nonzero verified on the valuation '
        'layer' % (len(polysA), badA))
    results['checks']['FR2A-members'] = len(polysA)

    # ------------------------- FR2 cell B: (3,11,2) SPLTAIL(5)
    phiB = [162, 9, 1]
    pinsB = [(27, 0), (0, 243), (27, 243), (54, 243)]
    bandsB = [(c * 3 ** 10, (12 if c else None)) for c in (0, 1, 2)]
    liftsB = [(0, 0, 0, 0),
              (0, 0, 0, 3 ** 11),                    # u = 11 = N
              (0, 0, 0, 2 * 3 ** 12),
              (0, 3 ** 12, 3 ** 11, 3 ** 14)]
    polysB, metasB = build_cell(3, 2, 11, phiB, pinsB, bandsB, liftsB)
    for tag, u, m in metasB:
        if u is not None and u < 11:
            viol('FR2B', '%s u_lift = %s < N = 11' % (tag, u))
        if m is not None and u is not None and u > m:
            viol('FR2B', '%s u_lift = %s > band m = %s' % (tag, u, m))
    sigsB = gp_sigmas(polysB, 3)
    badB = sum(1 for sg in sigsB if sg != SIG_SPLTAIL)
    for (tag, u, m), sg in zip(metasB, sigsB):
        if sg != SIG_SPLTAIL:
            viol('FR2B', '%s (u=%s m=%s): sigma %s' % (tag, u, m, sg))
    say('FR2B: (3,11,2) SPLTAIL(5): %d members (4 pins x 3 band '
        'digits in F_3 x 4 lifts): PARI sigma == {(1,2),(1,2)} on '
        'all (%d bad) -- first odd-q k>=2 exercise' % (len(polysB),
                                                       badB))
    results['checks']['FR2B-members'] = len(polysB)

    # ------------------------------------------- FR2 teeth
    tooth = []
    tooth.append(padd(padd(pmul(phiA, phiA),
                           pmul([128, 16], phiA)),
                      [1 << 13, 0]))                  # b0@13: RAM(13)
    tooth.append(padd(padd(pmul(phiA, phiA),
                           pmul([128, 16], phiA)),
                      [1 << 13, 1 << 13]))            # + band b1@13
    sg1, sg2 = gp_sigmas([t + [0] * (5 - len(t)) for t in tooth], 2)
    tooth3 = padd(padd(pmul(phiB, phiB), pmul([243, 27], phiB)),
                  [3 ** 9])                           # b0@9: RAM(9)
    tooth4 = padd(padd(pmul(phiB, phiB), pmul([243, 27], phiB)),
                  [3 ** 9, 3 ** 10])                  # + band
    sg3, sg4 = gp_sigmas([tooth3 + [0] * (5 - len(tooth3)),
                          tooth4 + [0] * (5 - len(tooth4))], 3)
    fired = 0
    for nm, sg in (('A-RAM13', sg1), ('A-RAM13+band', sg2),
                   ('B-RAM9', sg3), ('B-RAM9+band', sg4)):
        if sg != SIG_RAM_F:
            viol('FR2T', 'tooth %s sigma %s != {(2,2)}' % (nm, sg))
        if sg != SIG_SPLTAIL:
            fired += 1
    if fired != 4:
        viol('FR2T', 'teeth fired %d/4' % fired)
    say('FR2 TEETH: 4 wrong-floor mutants (b0@13 at cell A, b0@9 at '
        'cell B, each with/without a band digit): sigma = {(2,2)} '
        '(RAM) on all -- FIRED %d/4' % fired)
    results['checks']['FR2T-fired'] = fired

    # --------------- FR3: deep0 = q^{k-1} identity + grid law tie
    ngrid = nspl = 0
    for q in (2, 3, 5):
        for k in (1, 2, 3):
            for N in range(4 * k + 1, 4 * k + 7):
                A0all = list(range(4 * k + 1, N + k))
                nband = sum(1 for s in A0all if s > N)
                if nband != k - 1:
                    viol('FR3', 'band slots (q=%d,N=%d,k=%d) = %d '
                         '!= k-1' % (q, N, k, nband))
                mine = my_law_F(q, N, k)
                sealed = GC.law_F(q, N, k)
                ngrid += 1
                if mine != sealed:
                    viol('FR3', 'law tie fails at (%d,%d,%d)'
                         % (q, N, k))
                spl = [kk for kk in mine if kk[1] == 'SPLTAIL']
                if bool(spl) != (N >= 4 * k + 3):
                    viol('FR3', 'first-live boundary wrong at '
                         '(%d,%d,%d): %s' % (q, N, k, spl))
                if spl:
                    nspl += len(spl)
                    for kk in spl:
                        if mine[kk] % q ** (k - 1) != 0:
                            viol('FR3', 'deep0 does not divide %s '
                                 'at (%d,%d,%d)' % (kk, q, N, k))
    say('FR3: band slot count == k-1 IDENTICALLY on the grid (q in '
        '{2,3,5}, k in {1,2,3}, N in 4k+1..4k+6): %d cells, fresh == '
        'sealed law_F key-for-key on ALL; first-live boundary '
        '(SPLTAIL nonempty iff N >= 4k+3) exact; %d SPLTAIL keys '
        'all carry the q^{k-1} factor' % (ngrid, nspl))
    results['checks']['FR3-cells'] = ngrid

    # -------- FR4: counter-instances to R2's N-even band-pinned leg
    phiC = [16, 4, 1]
    # --- cell (2,8,2): u = N read structurally unrealizable; all
    # in-budget lifts have u = 9 = m -> RAM(9) -> {(2,2)} constant.
    pinsC = [(16, 0), (0, 64), (16, 64)]            # dv(A1) = 6
    polysC, metaC = [], []
    for pi, (pa1, pa0) in enumerate(pinsC):
        for li, (b0, b1) in enumerate(
                ((0, 1 << 7), (1 << 9, 1 << 7),
                 ((1 << 9) + (1 << 10), 1 << 7),
                 (0, (1 << 7) + (1 << 8)))):        # budgets: b0 >= 9
            F = padd(padd(pmul(phiC, phiC),
                          pmul([pa0, pa1], phiC)), [b0, b1])
            polysC.append(F + [0] * (5 - len(F)))
            metaC.append('c8-p%dL%d' % (pi, li))
    # --- cell (2,10,2): the refine-path adjudication (u = 10 lift).
    pinsE = [(32, 0), (0, 128), (32, 128)]          # dv(A1) = 7
    adjuds = []                                     # refine-path idx
    for pi, (pa1, pa0) in enumerate(pinsE):
        for li, b0 in enumerate((1 << 10, 0, 1 << 11,
                                 (1 << 10) + (1 << 12))):
            F = padd(padd(pmul(phiC, phiC),
                          pmul([pa0, pa1], phiC)), [b0, 1 << 9])
            if li in (0, 3):
                adjuds.append(len(polysC))          # u = 10 members
            polysC.append(F + [0] * (5 - len(F)))
            metaC.append('c10-p%dL%d' % (pi, li))
    contrastC = []
    for pa1, pa0 in pinsC:                          # band-ZERO, u=13
        F = padd(padd(pmul(phiC, phiC),
                      pmul([pa0, pa1], phiC)), [1 << 13, 0])
        contrastC.append(F + [0] * (5 - len(F)))
    for pa1, pa0 in pinsE:                          # band-ZERO, u=15
        F = padd(padd(pmul(phiC, phiC),
                      pmul([pa0, pa1], phiC)), [1 << 15, 0])
        contrastC.append(F + [0] * (5 - len(F)))
    sigsC = gp_sigmas(polysC + contrastC, 2)
    nbadC = 0
    for i, (tag, sg) in enumerate(zip(metaC, sigsC[:len(polysC)])):
        if sg != SIG_RAM_F:
            nbadC += 1
            viol('FR4', 'band-pinned %s: sigma %s != {(2,2)} '
                 '(verifier prediction wrong)' % (tag, sg))
    n_adj = sum(1 for i in adjuds if sigsC[i] == SIG_RAM_F)
    ncontra = 0
    for i, sg in enumerate(sigsC[len(polysC):]):
        if sg != SIG_SPLTAIL:
            viol('FR4', 'band-zero contrast %d: sigma %s != '
                 '{(1,2),(1,2)}' % (i, sg))
        else:
            ncontra += 1
    say('FR4 COUNTER-INSTANCES (R2 N-even band-pinned leg): %d/%d '
        'band-pinned lifts across (2,8,2) w=6 and (2,10,2) w=7 read '
        'sigma = {(2,2)} CONSTANT; the %d refine-path u=10 lifts at '
        "(2,10,2) -- where ANNEX R2's refine-deeper display "
        "predicts a fresh 2SIDED'(6,7) sigma = {(1,2),(1,2)} -- "
        'read {(2,2)} on %d/%d: the display is REFUTED at this '
        'stratum (verifier RAM(11) derivation CONFIRMED); at '
        '(2,8,2) the u = N = 8 read of R2\'s "Lift 2" is '
        'structurally unrealizable (entry budgets v(beta0) >= 9, '
        'v(beta1) >= 7 sit above both height-8 components); '
        'band-zero contrast members of the SAME keys: %d/%d '
        '{(1,2),(1,2)} (key-level differing pair EXISTS: '
        'clause-(c) conclusion survives cross-stratum)'
        % (len(polysC) - nbadC, len(polysC), len(adjuds), n_adj,
           len(adjuds), ncontra, len(contrastC)))
    results['checks']['FR4-members'] = len(polysC) + len(contrastC)

    # ------------- FR5: the Codex-cell (2,9,2) repaired witness
    pinsD = [(8, 0), (0, 32), (8, 32)]              # dv(A1) = 5
    polysD, metaD = [], []
    for pi, (pa1, pa0) in enumerate(pinsD):
        for li, b0 in enumerate((1 << 9, 0, 1 << 10)):
            F = padd(padd(pmul(phiC, phiC),
                          pmul([pa0, pa1], phiC)), [b0, 1 << 8])
            polysD.append(F + [0] * (5 - len(F)))
            metaD.append((pi, li))
    sigsD = gp_sigmas(polysD, 2)
    okD = 0
    for (pi, li), sg in zip(metaD, sigsD):
        if li == 0:
            if sg != SIG_RAM_F:
                viol('FR5', 'pin %d RAM(9) lift: sigma %s' % (pi, sg))
            else:
                okD += 1
        else:
            if sg not in (SIG_SPLTAIL, ((1, 4),)):
                viol('FR5', 'pin %d u=10 lift %d: sigma %s not '
                     'decided-nonRAM' % (pi, li, sg))
            else:
                okD += 1
    say('FR5 (Codex F4 cell, R2 N-odd leg): (2,9,2) w=5 band-pinned '
        'm=10=2w: RAM(9) lift {(2,2)} vs u=10 separable-read lifts '
        'decided {(1,2),(1,2)}/{(1,4)} on %d/%d members: the '
        'differing pair EXISTS exactly as R2 displays' % (okD,
                                                          len(polysD)))
    results['checks']['FR5-members'] = len(polysD)

    # ---------------------------------------------------- verdict
    dt = time.time() - t0
    verdict = 'GREEN' if not VIOL else 'RED'
    say('VERDICT: %s (%d violations) %.1fs' % (verdict, len(VIOL), dt))
    results['verdict'] = verdict
    results['violations'] = len(VIOL)
    results['elapsed_s'] = round(dt, 1)
    with open(os.path.join(HERE, 'genh4annexpass_fresh_output.txt'),
              'w') as fh:
        fh.write('\n'.join(LOG) + '\n')
    with open(os.path.join(HERE, 'genh4annexpass_fresh_results.json'),
              'w') as fh:
        json.dump(results, fh, indent=1, sort_keys=True, default=repr)
    return 0 if not VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
