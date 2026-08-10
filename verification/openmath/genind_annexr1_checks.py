#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
genind_annexr1_checks.py -- SEALED instrument for GENIND ANNEX R r1
(machine leg of ANNEX-LEMMA GENIND-C2: the CS-drain rate leg of
(A2-RATE)).

RUN WITH the openmath venv python (needs sympy):
  ../.venv-openmath/bin/python genind_annexr1_checks.py

CHARGE (GENIND_ANNEXR_pass_report.md GAP-1): R1.1 displays (A2-RATE)
on the FULL complement u_{mu,d}(M) while ANNEX-THEOREM GENIND.C'
proves the SIMPLE slice; the CS-stratum drain component's all-window
rate was supplied nowhere displayed.  The r1 annex derives it
(ANNEX-LEMMA GENIND-C2); this instrument is that lemma's machine leg.

TWO-COMMIT SEAL: commit 1 = this runner UNRUN (no full run before the
seal; smoke record below) + the annex r1 text with the machine record
slot PENDING; commit 2 = verdict appended FROM the committed
artifacts (genind_annexr1_output.txt / genind_annexr1_results.json).
PRE-SEAL SMOKE record: sanity of the arithmetic helpers only (mstar/
bounds at 3 hand points, sympy P5 identity once); NO consE/consF row
was run before the seal.

DESIGN: the pinned GENH4 sealed walker genh4_checks.py (the
[GENIND-H(4)] discharge battery; imported READ-ONLY -- its own
per-row law checks incl. GH-UND stay live at my fresh rows and must
stay SILENT) is run at FRESH (kind,q,N,h/k) rows disjoint from its
committed roster; my checks consume only the returned UND tallies.
The committed deep row (Zp,2,11,h=5) is read from
genh4_checks_results.json at its worktree pin for tooth T-WIN.

GENIND-C2 quantities under test (E := CS4-E, F := CS4-F):
  E: |K| = q,   M* = 2N-2-4h   (dv-window 2N-2 minus the GENIND-4
                                node depth dv(A0) >= 4h+1)
  F: |K| = q^2, M* = N-1-4k    (v-window N-1 minus the height
                                v(a0) = 4k node floor)
  bound per stratum: UND <= entry * M* * |K|^-(M*-1)   [M* >= 2]
  M* <= 1 rows are FLOOR-ADJACENT: trivial bound = entry; recorded,
  not P1-scored (the entry mass itself carries the decay there).

PREREGISTERED CHECKS (fixed before any run; expected outcomes in
parens):
 P1 WINDOW  per fresh row with M* >= 2: UND <= entry*M*/|K|^(M*-1)
            (expect GREEN with margin ~ q^-(N-2h) at E rows).
 P2 SPECIES per (q,N): total swept UND / q^(4(N-1)) <= N*q^-(N-2)
            (the (A2-RATE) species at (K,B,c)=(1,1,2), CS-drain leg).
 P3 SLOPE   fixed (genre,q,h/k), consecutive swept N with both
            M* >= 2: UND_rel(N+1)/UND_rel(N) <= q^-1.5.  This is the
            scenario-killer: window-deficit slope <= 1 gives ratio
            >= q^-1, REFUSED here.  (Expected measured ratio ~ q^-3.)
 P4 N5-GEO  sympy + grid: CS5-V1E2 entry_rel identity
            (q-1)q^(4N-5h-3)(q^(N-(5h+1)/2)-1)/q^(5(N-1)) ==
            (q-1)q^(2-(15h+1)/2)(1-q^-(N-(5h+1)/2))  [constant-order
            in N: the S5.2 positive-density display], and the
            composed CS5 drain bound sum_h entry_rel*min(1,M*q^-(M*-1))
            <= N*q^-(N-1) at q in {2,3,7}, h odd, N <= 40.
 P5 C1-TIE  sympy: q^-(D-1)*M^B*q^-(M-c) == M^B*q^-(N-c-1) under
            D+M=N (GENIND-C1(iii)'s composition, consumed at the
            n=5 (4,d) child with the C2-completed full rate).
TEETH (each must fire >= 1 or the verdict is RED):
 T-SLOPE  the GAP-1 failure scenario made flesh: fake n=4 E-drain at
          window-deficit slope 1/2, UND_fake = entry*q^-ceil((N-1-2h)/2),
          must VIOLATE the P1 bound at (Zp,2,N=7,h=1).
 T-WIN    mis-derived stage window M*wrong = 2N-2-2h must be REFUTED
          by the committed row (Zp,2,11,h=5): UND 32768 vs bound
          entry*M*wrong*q^-(M*wrong-1) = 65536*10*2^-9 = 1280.

FRESH ROSTER (all Zp; entry = (q-1)q^(4N-5h-3) for E,
q(q-1)/2 * q^(4N-10k-4) * [#psi handled by the walker] for F):
  E q=2 h=1 N=4,5,6,7   (M* = 2,4,6,8;  members 2^8..2^20)
  E q=2 h=3 N=8,9       (M* = 2,4;      members 2^14, 2^18)
  E q=3 h=1 N=4,5       (M* = 2,4;      members 2*3^8, 2*3^12)
  F q=2 k=1 N=7,8,9     (M* = 2,3,4;    members 2^14, 2^18, 2^22)
  F q=3 k=1 N=6         (M* = 1 FLOOR-ADJ, P2 only; members 3^11)
"""

import sys, os, json, time, math

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import genh4_checks as GH  # pinned sealed walker, READ-ONLY consumption
import hashlib


def md5(fn):
    with open(os.path.join(HERE, fn), 'rb') as f:
        return hashlib.md5(f.read()).hexdigest()


CHECKS = ['C2-PIN', 'C2-P1', 'C2-P2', 'C2-P3', 'C2-P4', 'C2-P5']
TEETH = ['T-SLOPE', 'T-WIN']
VIOL = {c: [] for c in CHECKS}
NCHK = {c: 0 for c in CHECKS}
FIRE = {t: 0 for t in TEETH}


def say(m):
    print(m)
    sys.stdout.flush()


def note(c, n=1):
    NCHK[c] += n


def viol(c, tag, d):
    VIOL[c].append((tag, d))
    say('  VIOLATION [%s] %s: %s' % (c, tag, d))


def und_of(obs):
    return sum(c for kk, c in obs.items() if len(kk) > 4 and kk[4] == 'UND')


def mstar(genre, N, hk):
    return (2 * N - 2 - 4 * hk) if genre == 'E' else (N - 1 - 4 * hk)


def kabs(genre, q):
    return q if genre == 'E' else q * q


def p1_bound(genre, q, N, hk, entry):
    M = mstar(genre, N, hk)
    if M < 2:
        return None  # floor-adjacent: trivial bound = entry
    return entry * M * kabs(genre, q) ** (-(M - 1))


ROSTER = [('E', 2, 4, 1), ('E', 2, 5, 1), ('E', 2, 6, 1), ('E', 2, 7, 1),
          ('E', 2, 8, 3), ('E', 2, 9, 3),
          ('E', 3, 4, 1), ('E', 3, 5, 1),
          ('F', 2, 7, 1), ('F', 2, 8, 1), ('F', 2, 9, 1),
          ('F', 3, 6, 1)]


def main():
    t00 = time.time()
    say('== C2-PIN')
    pins = {'genh4_checks.py': md5('genh4_checks.py'),
            'genh4_checks_results.json': md5('genh4_checks_results.json'),
            'genind_checks.py': md5('genind_checks.py')}
    for fn, h in pins.items():
        note('C2-PIN')
        say('  %s %s' % (h[:8], fn))
    if pins['genind_checks.py'][:8] != 'e7ca150b':
        viol('C2-PIN', 'runner', 'genind_checks.py moved off e7ca150b')

    say('== fresh rows (pinned GENH4 walker, read-only)')
    rows = {}
    gh_viol0 = sum(len(v) for v in GH.VIOL.values())
    for genre, q, N, hk in ROSTER:
        fn = GH.run_consE if genre == 'E' else GH.run_consF
        rowdict, obs = fn('Zp', q, N, hk)
        entry = rowdict['members']
        und = und_of(obs)
        rows[(genre, q, N, hk)] = (entry, und)
        say('  row %s q=%d N=%d %s=%d: entry %d UND %d M*=%d'
            % (genre, q, N, 'h' if genre == 'E' else 'k', hk,
               entry, und, mstar(genre, N, hk)))
    gh_viol1 = sum(len(v) for v in GH.VIOL.values())
    note('C2-PIN')
    if gh_viol1 != gh_viol0:
        viol('C2-PIN', 'walker', 'pinned walker flagged %d violations '
             'at my fresh rows' % (gh_viol1 - gh_viol0))

    say('== C2-P1 window bound')
    for (genre, q, N, hk), (entry, und) in sorted(rows.items()):
        b = p1_bound(genre, q, N, hk, entry)
        if b is None:
            say('  P1 %s q=%d N=%d: FLOOR-ADJACENT (M*<=1), not scored'
                % (genre, q, N))
            continue
        note('C2-P1')
        if und > b:
            viol('C2-P1', '%s,%d,%d,%d' % (genre, q, N, hk),
                 'UND %d > bound %.3f' % (und, b))

    say('== C2-P2 species bound per (q,N)')
    byqn = {}
    for (genre, q, N, hk), (entry, und) in rows.items():
        byqn.setdefault((q, N), 0)
        byqn[(q, N)] += und
    for (q, N), tot in sorted(byqn.items()):
        note('C2-P2')
        rel = tot / float(q ** (4 * (N - 1)))
        bound = N * q ** (-(N - 2))
        say('  P2 q=%d N=%d: swept UND_rel %.3e vs N*q^-(N-2) %.3e'
            % (q, N, rel, bound))
        if rel > bound:
            viol('C2-P2', '%d,%d' % (q, N), '%.3e > %.3e' % (rel, bound))

    say('== C2-P3 slope (the scenario-killer)')
    for genre, q, hk in [('E', 2, 1), ('E', 2, 3), ('E', 3, 1),
                         ('F', 2, 1)]:
        Ns = sorted(N for (g, qq, N, h) in rows
                    if g == genre and qq == q and h == hk
                    and mstar(genre, N, hk) >= 2)
        for N0, N1 in zip(Ns, Ns[1:]):
            if N1 != N0 + 1:
                continue
            note('C2-P3')
            e0, u0 = rows[(genre, q, N0, hk)]
            e1, u1 = rows[(genre, q, N1, hk)]
            if u0 == 0:
                viol('C2-P3', 'zero', '%s q=%d N=%d UND=0' % (genre, q, N0))
                continue
            r = (u1 / float(q ** (4 * N1 - 4))) \
                / (u0 / float(q ** (4 * N0 - 4)))
            cap = q ** (-1.5)
            slope = -math.log(r, q)
            say('  P3 %s q=%d %s=%d N %d->%d: ratio %.4g '
                '(measured slope %.2f; cap q^-1.5=%.4g)'
                % (genre, q, 'h' if genre == 'E' else 'k', hk,
                   N0, N1, r, slope, cap))
            if r > cap:
                viol('C2-P3', '%s,%d,%d->%d' % (genre, q, N0, N1),
                     'ratio %.4g > %.4g (slope <= 1.5 NOT excluded)'
                     % (r, cap))

    say('== C2-P4 n=5 geography (CS5-V1E2), sympy + grid')
    import sympy as sp
    qs, Ns_, hs = sp.symbols('q N h', positive=True)
    lhs = (qs - 1) * qs ** (4 * Ns_ - 5 * hs - 3) \
        * (qs ** (Ns_ - (5 * hs + 1) / 2) - 1) / qs ** (5 * (Ns_ - 1))
    rhs = (qs - 1) * qs ** (2 - (15 * hs + 1) / 2) \
        * (1 - qs ** (-(Ns_ - (5 * hs + 1) / 2)))
    note('C2-P4')
    if sp.simplify(lhs - rhs) != 0:
        viol('C2-P4', 'entry-identity', 'V1E2 entry_rel rewrite failed')
    for q in (2, 3, 7):
        for N in range(4, 41):
            tot = 0.0
            for h in range(1, N, 2):
                if 2 * h > N - 1 or 2 * N <= 5 * h + 1:
                    continue
                erel = (q - 1) * q ** (2 - (15 * h + 1) / 2.0) \
                    * (1 - q ** (-(N - (5 * h + 1) / 2.0)))
                M = 2 * N - 2 - 4 * h
                stage = min(1.0, M * q ** (-(M - 1.0))) if M >= 1 else 1.0
                tot += erel * stage
            note('C2-P4')
            if tot > N * q ** (-(N - 1.0)):
                viol('C2-P4', 'compose,%d,%d' % (q, N),
                     '%.3e > %.3e' % (tot, N * q ** (-(N - 1.0))))

    say('== C2-P5 C1(iii) composition identity')
    D, M, Nv, c, B = sp.symbols('D M Nv c B', positive=True)
    expr = qs ** (-(D - 1)) * M ** B * qs ** (-(M - c))
    note('C2-P5')
    if sp.simplify(expr.subs(D, Nv - M)
                   - M ** B * qs ** (-(Nv - c - 1))) != 0:
        viol('C2-P5', 'identity', 'D+M=N composition failed')

    say('== TEETH')
    genre, q, N, hk = 'E', 2, 7, 1
    entry, _ = rows[(genre, q, N, hk)]
    fake = entry * q ** (-math.ceil((N - 1 - 2 * hk) / 2.0))
    b = p1_bound(genre, q, N, hk, entry)
    if fake > b:
        FIRE['T-SLOPE'] += 1
        say('  T-SLOPE FIRED: fake slope-1/2 drain %d > P1 bound %.1f'
            % (fake, b))
    with open(os.path.join(HERE, 'genh4_checks_results.json')) as f:
        committed = json.load(f)
    deep = None
    for r in committed['rows']:
        if r.get('row') == 'consE Zp q=2 N=11 h=5':
            import ast
            deep = (r['members'],
                    sum(cc for ks, cc in r['keys'].items()
                        if ast.literal_eval(ks)[4] == 'UND'))
    if deep:
        entry11, und11 = deep
        Mw = 2 * 11 - 2 - 2 * 5
        bw = entry11 * Mw * 2 ** (-(Mw - 1))
        if und11 > bw:
            FIRE['T-WIN'] += 1
            say('  T-WIN FIRED: committed (2,11,5) UND %d > wrong-window '
                'bound %.1f (M*wrong=%d)' % (und11, bw, Mw))
    else:
        viol('C2-PIN', 'T-WIN', 'committed deep row not found')

    say('== VERDICT')
    nv = sum(len(v) for v in VIOL.values())
    dead = [t for t in TEETH if FIRE[t] == 0]
    verdict = 'GREEN' if nv == 0 and not dead else 'RED'
    say('checks: ' + ' '.join('%s %d/%d' % (c, NCHK[c], len(VIOL[c]))
                              for c in CHECKS))
    say('teeth:  ' + ' '.join('%s %d' % (t, FIRE[t]) for t in TEETH))
    say('%s: %d violations, %d dead teeth (%.1fs)'
        % (verdict, nv, len(dead), time.time() - t00))
    out = {'pins': pins,
           'rows': {'%s,%d,%d,%d' % k: v for k, v in sorted(rows.items())},
           'checks': {c: [NCHK[c], len(VIOL[c])] for c in CHECKS},
           'viol': {c: VIOL[c] for c in CHECKS if VIOL[c]},
           'teeth': FIRE, 'verdict': verdict,
           'elapsed_s': round(time.time() - t00, 1)}
    with open(os.path.join(HERE, 'genind_annexr1_results.json'), 'w') as f:
        json.dump(out, f, indent=1, sort_keys=True)
    return 0 if verdict == 'GREEN' else 1


if __name__ == '__main__':
    sys.exit(main())
