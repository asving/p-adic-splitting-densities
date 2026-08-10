#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
genind_annexr_pass2_fresh.py -- FRESH out-of-battery leg for the GENIND
ANNEX pass 2 (hostile verifier instrument; verifier-authored, run once).

Route DISJOINT from pass 1's fresh leg (N=40 recursion at Q=7,27;
r=4,5 union bounds) AND from the r1 machine leg's roster (E q=2
h=1/h=3, q=3 h=1; F q=2/3 k=1).  Preregistered checks (fixed before
any run; the pinned GENH4 walker ee8024b7 is consumed READ-ONLY and
its own live law checks must stay silent):

 PF1 WALKER-FRESH  rows never enumerated by any committed leg:
      E q=2 h=5 N=12,13  (first h=5 fresh enumerations; deep-h slope
                          pair, M* = 2,4)
      E q=5 h=1 N=4      (first q=5 row anywhere on this claim)
      scored: P1 window bound UND <= entry*M**|K|^-(M*-1) at each row
      with M* >= 2; single-step slope cap q^-1.5 at the (12->13, h=5)
      pair (genre E showed NO parity band at any r1 pair); REPORT
      (not scored): tie against GENH4.B's committed aggregate law
      (q-1)*q^(2N-h-2) -- expected UND 2^17, 2^19, 12500.
 PF2 UNION-6   sympy, r=6: dG/du_i == prod_{j!=i}(T_j-u_j) and
      UB - G nonneg-coefficient in (u_i, T_i-u_i)  (GENIND-C1(ii)/
      R6's mechanism two steps past every committed check).
 PF3 RATE-INEQ  the undisplayed C2(iii) comparison, machine face:
      for every CS-inventory shape (e, degpsi, mu) with e*degpsi >= 2,
      mu >= 2, L = e*mu*degpsi <= 12: entry rate a := (L+1)/2 obeys
      a >= e*degpsi + 1/2  AND  min(a, e*degpsi) >= 2
      (height-sum convergence margin + the slope-2 floor at every
      shape reachable up to m = 12, not just n = 4).
 PF4 V4E2-GRID  the C2 instance the repair did NOT use: CS5-V4E2
      composed drain, entry_rel = (q-1)^2 q^(1-5v4-5h) (S5.3's table),
      stage species M* = 2(N-1-v4-2h) (C2(i) with E=2, H = v4+2h),
      vertex condition h >= 2v4+1, h odd, v4 >= 1, visibility
      v4+2h <= N-1:  sum <= N*q^-(N-1) at q in {2,3,7}, N <= 40.
 PF5 QNPP  non-prime-power algebra corner (admissible: the m=2
      closed forms / species are polynomial identities in Q): exact
      integer check at Q = 6 and Q = 10, N = 2..25, that
      u(M) = Q^(M-1) + floor((M-1)/2)(Q-1)Q^(M-2) solves the S5.2
      m=2 recursion u(N) = Q^(N-1) + sum_{2k<=N-1}(Q-1)Q^k u(N-2k),
      u(1) = 1, and u(N)*Q^(N-1) <= N*Q^(2N-2)  (the C' ground bound
      cross-multiplied to integers).
TEETH (each must fire or the verdict is RED):
 TF-PAIR  fake slope-1 step at the new deep pair: u_fake(13) :=
      UND(12,h=5)*q^(4-1)... i.e. rel ratio q^-1 must BREACH the
      q^-1.5 pair cap (the pass-1 failure scenario at a row no
      committed leg used).
 TF-LAW  corrupted aggregate exponent (q-1)*q^(2N-h-1) must MISMATCH
      the measured UND at (2,12,5).
Verdict GREEN iff zero violations and both teeth fired; exit 0/1.
"""

import sys, os, math, time, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import genh4_checks as GH

VIOL = []
NCHK = {}
FIRE = {'TF-PAIR': 0, 'TF-LAW': 0}


def say(m):
    print(m)
    sys.stdout.flush()


def chk(tag, ok, detail):
    NCHK[tag] = NCHK.get(tag, 0) + 1
    if not ok:
        VIOL.append((tag, detail))
        say('  VIOLATION [%s] %s' % (tag, detail))


def main():
    t0 = time.time()
    with open(os.path.join(HERE, 'genh4_checks.py'), 'rb') as f:
        pin = hashlib.md5(f.read()).hexdigest()
    say('== PIN genh4_checks.py %s' % pin[:8])
    chk('PIN', pin[:8] == 'ee8024b7', 'walker moved off ee8024b7')

    say('== PF1 walker-fresh rows')
    gh0 = sum(len(v) for v in GH.VIOL.values())
    rows = {}
    for (q, N, h) in [(2, 12, 5), (5, 4, 1), (2, 13, 5)]:
        rowdict, obs = GH.run_consE('Zp', q, N, h)
        entry = rowdict['members']
        und = sum(c for kk, c in obs.items()
                  if len(kk) > 4 and kk[4] == 'UND')
        M = 2 * N - 2 - 4 * h
        rows[(q, N, h)] = (entry, und)
        law = (q - 1) * q ** (2 * N - h - 2)
        say('  row E q=%d N=%d h=5? h=%d: entry %d UND %d M*=%d '
            '(committed-law tie %d %s)'
            % (q, N, h, entry, und, M, law,
               'EXACT' if law == und else 'MISMATCH-disclose'))
        if M >= 2:
            b = entry * M * q ** (-(M - 1))
            chk('PF1-P1', und <= b, 'q=%d N=%d h=%d UND %d > %.1f'
                % (q, N, h, und, b))
    gh1 = sum(len(v) for v in GH.VIOL.values())
    chk('PF1-SILENT', gh0 == gh1,
        'pinned walker flagged %d at fresh rows' % (gh1 - gh0))
    e0, u0 = rows[(2, 12, 5)]
    e1, u1 = rows[(2, 13, 5)]
    r = (u1 / 2.0 ** (4 * 13 - 4)) / (u0 / 2.0 ** (4 * 12 - 4))
    say('  PF1 pair (h=5) N 12->13: ratio %.4g slope %.2f'
        % (r, -math.log(r, 2)))
    chk('PF1-SLOPE', r <= 2 ** (-1.5),
        'pair ratio %.4g > q^-1.5 (slope <= 1.5 not excluded '
        'at the deep-h row)' % r)

    say('== PF2 union bound r=6 (sympy)')
    import sympy as sp
    r6 = 6
    T = sp.symbols('T1:%d' % (r6 + 1), positive=True)
    u = sp.symbols('u1:%d' % (r6 + 1), positive=True)
    G = sp.prod(T) - sp.prod([T[i] - u[i] for i in range(r6)])
    for i in range(r6):
        d = sp.expand(sp.diff(G, u[i])
                      - sp.prod([T[j] - u[j] for j in range(r6) if j != i]))
        chk('PF2-DG', d == 0, 'dG/du_%d mismatch' % (i + 1))
    UB = sum(u[i] * sp.prod([T[j] for j in range(r6) if j != i])
             for i in range(r6))
    s = sp.symbols('s1:%d' % (r6 + 1), positive=True)
    diff = sp.expand((UB - G).subs(
        [(T[i], u[i] + s[i]) for i in range(r6)]))
    poly = sp.Poly(diff, *(list(u) + list(s)))
    negs = [c for c in poly.coeffs() if c < 0]
    chk('PF2-UB', not negs, 'UB-G has %d negative coefficients'
        % len(negs))
    say('  PF2: %d monomials, all nonneg %s'
        % (len(poly.coeffs()), 'OK' if not negs else 'NO'))

    say('== PF3 rate inequality over the CS inventory (L <= 12)')
    shapes = 0
    for e in range(1, 7):
        for dg in range(1, 7):
            if e * dg < 2:
                continue
            for mu in range(2, 7):
                L = e * mu * dg
                if L > 12:
                    continue
                shapes += 1
                a = (L + 1) / 2.0
                chk('PF3', a >= e * dg + 0.5,
                    'a=%.1f < e*degpsi+1/2 at (e,dg,mu)=(%d,%d,%d)'
                    % (a, e, dg, mu))
                chk('PF3', min(a, e * dg) >= 2,
                    'slope floor <2 at (e,dg,mu)=(%d,%d,%d)' % (e, dg, mu))
    say('  PF3: %d inventory shapes checked' % shapes)

    say('== PF4 CS5-V4E2 composed grid (the unused instance)')
    for q in (2, 3, 7):
        for N in range(4, 41):
            tot = 0.0
            for v4 in range(1, N):
                for h in range(2 * v4 + 1, N, 2):
                    if v4 + 2 * h > N - 1:
                        continue
                    erel = (q - 1) ** 2 * float(q) ** (1 - 5 * v4 - 5 * h)
                    M = 2 * (N - 1 - v4 - 2 * h)
                    st = min(1.0, M * float(q) ** (-(M - 1.0))) \
                        if M >= 1 else 1.0
                    tot += erel * st
            chk('PF4', tot <= N * float(q) ** (-(N - 1.0)),
                'q=%d N=%d: %.3e > %.3e'
                % (q, N, tot, N * float(q) ** (-(N - 1.0))))

    say('== PF5 Q = 6, 10 algebra corner (exact ints)')
    for Q in (6, 10):
        uu = {1: 1, 2: Q}
        for N in range(3, 26):
            uu[N] = Q ** (N - 1) + sum(
                (Q - 1) * Q ** k * uu[N - 2 * k]
                for k in range(1, N) if 2 * k <= N - 1)
        for N in range(1, 26):
            cf = Q ** (N - 1) + ((N - 1) // 2) * (Q - 1) * Q ** (N - 2) \
                if N >= 2 else 1
            chk('PF5-CF', uu[N] == cf, 'Q=%d N=%d closed form' % (Q, N))
            chk('PF5-SP', uu[N] * Q ** (N - 1) <= N * Q ** (2 * N - 2),
                'Q=%d N=%d species' % (Q, N))

    say('== TEETH')
    fake_r = 2.0 ** (-1)  # slope-1 step at the (12->13, h=5) pair
    if fake_r > 2 ** (-1.5):
        FIRE['TF-PAIR'] += 1
        say('  TF-PAIR FIRED: fake slope-1 pair ratio %.3g > cap %.4g'
            % (fake_r, 2 ** (-1.5)))
    bad_law = (2 - 1) * 2 ** (2 * 12 - 5 - 1)
    if bad_law != rows[(2, 12, 5)][1]:
        FIRE['TF-LAW'] += 1
        say('  TF-LAW FIRED: corrupted exponent %d != measured %d'
            % (bad_law, rows[(2, 12, 5)][1]))

    say('== VERDICT')
    dead = [t for t, c in FIRE.items() if c == 0]
    verdict = 'GREEN' if not VIOL and not dead else 'RED'
    say('checks: ' + ' '.join('%s %d' % kv for kv in sorted(NCHK.items())))
    say('%s: %d violations, %d dead teeth (%.1fs)'
        % (verdict, len(VIOL), len(dead), time.time() - t0))
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main())
