#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
genh4_checks.py -- SEALED BATTERY for GENH4_PROOF_2026-08-08.md
(the [GENIND-H(4)] discharge: Q22-L1/L2/L3 proved at both quartic
composite genres, sigma by the resolvent method, P-D settled
unreachable at n=4, and the quartic densities R_tau(q)).

RUN WITH the openmath venv python (needs sympy):
  ../.venv-openmath/bin/python genh4_checks.py [--smoke]

TWO-COMMIT SEAL.  Commit 1 = this runner + the note sealed with
preregistered predictions, battery UNRUN on the full roster; commit 2
= verdict appended FROM the committed artifacts
(genh4_checks_output.txt / genh4_checks_results.json).

DESIGN DISCLOSURES:
 * The committed QSCOUT22 artifacts are consumed as the ROSTER TIE:
   my own law evaluator (fresh code from the note's S6 closed forms;
   the qscout22 model functions are never called) must reproduce
   every committed composite key.  Fresh rows are READ with the
   md5-pinned qscout22 reader read22 (GREEN + PARI-tied at its seal;
   reader-reimplementation seam disclosed in the note GENH4-BOX-5) --
   EXCEPT the GH-REFINE rows, which are walked by THIS runner's own
   independent stage walker (own division, own residual reads, own
   refine formulas) and cross-checked against read22 per member.
 * GH-CROSS (a fresh 16.7M full sweep at (Zp,2,7)) was considered and
   DROPPED for runtime budget; disclosed here per the note S12.
 * PRE-SEAL SMOKE record: smoke = GH-PIN + JSON tie on all 23
   committed rows + fresh consE (Zp,7,3,1) + consF (Zp,2,9,2) +
   GH-REFINE (Zp,2,6,1) + GH-PD + GH-DENS symbolic + oracle.
   Smoke run 1: RED with two development findings, both folded in
   and disclosed (note S8/S12): (a) the in-vitro cascade claim was
   TOO STRONG -- the mixed-char +2w term and (run 2, Fqt) the
   equal-char odd-dmu CARRY C = wc^2 both revive A1; the true forced
   statement is all-even-H2 only; (b) sympy Sum().doit() Piecewise
   artifacts replaced by explicit geometric closed forms (the
   partition-of-unity identity adjudicates them).
   FINAL SMOKE: GREEN, 17.4 s, 0 violations in all families
   (GH-JSONTIE 481 law-key checks, GH-REFINE 87,040 checks /
   10,752 refine events, GH-SIGMA 2,055 scored 0 bad), all five
   teeth fired (LAT 16 / CEN 12 / ALPH 3 / SIG 1 / DENS 1); the
   R_tau forms printed at smoke were pasted verbatim into the note
   S9.4 at the seal.  No full-roster run before the seal.

FAMILIES:
  GH-PIN     [NONE] md5 pins (qscout22 runner + artifacts, w10, w12,
             om_density_engine)
  GH-JSONTIE [SAME] my S6 laws == every committed qscout22 key
             (all 23 rows, both directions, order-1 + composite)
  GH-FRESH   [SAME] fresh never-measured rows == my laws (q=7 entries,
             deep h=5, k=2, fresh full sweep (Fqt,5,3))
  GH-PRE2    [SAME] depth-2 prehistory (Zp,2,11,pre=(1,2)): the
             (q-1)^2 floored fresh law at r=2
  GH-REFINE  [SAME] the GENH4-4 one-step refine formulas POINTWISE
             (own walker; carry + twist-kill checked digit-by-digit;
             final key == pinned reader's)
  GH-FEVEN   [SAME] odd-q even-dmu genre-F stratum (Zp,3,7,k=1),
             constructed THROUGH the GENH4-1F development map
  GH-PD      [SAME] S1-slot liveness scan (GENH4-6) + char-2
             '1sq' <=> S1=0 pointwise + the in-vitro cascade locus
  GH-UND     [SAME] THEOREM GENH4.B closed forms vs every UND key
  GH-BRACKET [SYM]  the CS-2 bracket: aggregated-vs-resolved key sums
  GH-DENS    [SYM/IND] block vectors, nu4 == beta(4) (pinned engine),
             Sigma_tau R_tau = 1 symbolic, partial-sum sandwich
  GH-SIGMA   [IND]  PARI sigma per decided member on fresh rows
TEETH (each must fire >= 1 or RED):
  GH-T-LAT   law_E on the integer-only dv ladder must mismatch
  GH-T-CEN   E-INERT census q(q-1)/2 -> q(q-1) must mismatch
  GH-T-ALPH  law_F censuses over F_q instead of F_{q^2} must mismatch
             (incl. the odd-q GH-FEVEN row)
  GH-T-SIG   F-RAM sigma flipped {(2,2)}->{(1,4)} caught by PARI
  GH-T-DENS  corrupted E-stage census must break the beta4 tie
"""

import sys, os, json, time, hashlib, itertools, ast
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))   # for om_density_engine

import qscout22_checks as Q
import w10_checks as W10
import w12_checks as W12

PINS = {
    'qscout22_checks.py': 'cb885663dd4ef6dfda9c28a67c1a076e',
    'qscout22_results.json': '6c2441a12cf52ffd43055de912a4affe',
    'qscout22_output.txt': '378a12b30b1ee3e1d3b929835827c7c7',
    'w10_checks.py': 'a9c34244a3af19f5fa864375b494380b',
    'w12_checks.py': '7dc040d94fbbb1e8d20ac817b665d418',
    '../om_density_engine.py': '7240a916060c360d4433ca8a802d315d',
}

FAMILIES = ['GH-PIN', 'GH-JSONTIE', 'GH-FRESH', 'GH-PRE2', 'GH-REFINE',
            'GH-FEVEN', 'GH-PD', 'GH-UND', 'GH-BRACKET', 'GH-DENS',
            'GH-SIGMA']
TEETH = ['GH-T-LAT', 'GH-T-CEN', 'GH-T-ALPH', 'GH-T-SIG', 'GH-T-DENS']
VIOL = {f: [] for f in FAMILIES}
NCHK = {f: 0 for f in FAMILIES}
FIRE = {t: 0 for t in TEETH}
LOG = []


def say(m):
    print(m)
    sys.stdout.flush()
    LOG.append(m)


def note(f, n=1):
    NCHK[f] += n


def viol(f, tag, d):
    VIOL[f].append((tag, d))
    say('  VIOLATION [%s] %s: %s' % (f, tag, d))


# ================= MY LAW LAYER (fresh code from the note's S6) ======
def slots_E(q, N, h):
    A1 = sorted([2 * v + h for v in range((h + 1) // 2, N)]
                + [2 * v for v in range(h + 1, N)])
    A0 = sorted([2 * v + h for v in range((3 * h + 1) // 2, N)]
                + [2 * v for v in range(2 * h + 1, N)])
    return A1, A0


def law_E(q, N, h, f1init=None, f0init=None, integer_only=False,
          inert_c=None):
    """per (center, entry letter): dict (H2, leaf, params) -> count."""
    A1all, A0all = slots_E(q, N, h)
    if integer_only:
        A1all = [s for s in A1all if s % 2 == 0]
        A0all = [s for s in A0all if s % 2 == 0]
    c11 = (q - 1) * (q - 2) // 2
    c2 = q * (q - 1) // 2 if inert_c is None else inert_c
    out = {}

    def put(k, v):
        if v:
            out[k] = out.get(k, 0) + v

    def rec(f1, f0, wt, H2):
        A1 = [s for s in A1all if s > f1]
        A0 = [s for s in A0all if s > f0]
        deep0 = len([s for s in A0 if s >= 2 * N])
        for dv1 in A1:
            if dv1 < N:
                put((H2, 'SPLTAIL', (dv1,)), wt * (q - 1)
                    * q ** (deep0 + len([s for s in A1 if s > dv1])))
        put((H2, 'UND', ()),
            wt * q ** (deep0 + len([s for s in A1 if s >= N])))
        for dv0 in A0:
            if dv0 >= 2 * N:
                continue
            nz0 = len([s for s in A0 if s > dv0])
            if dv0 % 2 == 1:
                put((H2, 'RAM', (dv0,)), wt * (q - 1)
                    * q ** (nz0 + len([s for s in A1 if 2 * s > dv0])))
            for dv1 in A1:
                if 2 * dv1 < dv0:
                    put((H2, '2SIDED', (dv1, dv0 - dv1)),
                        wt * (q - 1) ** 2
                        * q ** (nz0 + len([s for s in A1 if s > dv1])))
            if dv0 % 2 == 0:
                dmu = dv0 // 2
                base = wt * q ** (nz0 + len([s for s in A1 if s > dmu]))
                put((H2, 'SPLITEQ', (dmu,)), base * c11)
                put((H2, 'INERT', (dmu,)), base * c2)
                rec(dmu, dv0, wt * (q - 1), H2 + (dmu,))

    rec(f1init if f1init is not None else 2 * h,
        f0init if f0init is not None else 4 * h, 1, ())
    if not integer_only and inert_c is None and f1init is None:
        assert sum(out.values()) == q ** (len(A1all) + len(A0all))
    return out


def law_F(q, N, k, f0init=None, alphabet_q=False):
    """per (psi): dict (H2, leaf, params) -> count."""
    Qa = q if alphabet_q else q * q
    A1all = list(range(2 * k + 1, N + k))
    A0all = list(range(4 * k + 1, N + k))
    comp = lambda m: 2 if m <= N - 1 else 1
    c11 = (Qa - 1) * (Qa - 2) // 2
    c2 = Qa * (Qa - 1) // 2
    out = {}

    def put(kk, v):
        if v:
            out[kk] = out.get(kk, 0) + v

    def wf(av, lo):
        return q ** sum(comp(s) for s in av if s > lo)

    def rec(f1, f0, wt, H2):
        A1 = [s for s in A1all if s > f1]
        A0 = [s for s in A0all if s > f0]
        deep0 = q ** sum(comp(s) for s in A0 if s > N)
        for dv1 in A1:
            if 2 * dv1 < N:
                put((H2, 'SPLTAIL', (dv1,)),
                    wt * (q ** comp(dv1) - 1) * wf(A1, dv1) * deep0)
        put((H2, 'UND', ()), wt * deep0
            * q ** sum(comp(s) for s in A1 if 2 * s >= N))
        for dv0 in A0:
            if dv0 > N:
                continue
            nz0 = wf(A0, dv0)
            ex0 = q ** comp(dv0) - 1
            if dv0 % 2 == 1:
                put((H2, 'RAM', (dv0,)), wt * ex0 * nz0
                    * q ** sum(comp(s) for s in A1 if 2 * s > dv0))
            for dv1 in A1:
                if 2 * dv1 < dv0:
                    put((H2, '2SIDED', (dv1, dv0 - dv1)),
                        wt * (q ** comp(dv1) - 1) * ex0
                        * wf(A1, dv1) * nz0)
            if dv0 % 2 == 0:
                dmu = dv0 // 2
                on1 = q ** sum(comp(s) for s in A1 if s > dmu)
                if dv0 == N:
                    put((H2, 'UND', ()),
                        wt * q ** comp(dmu) * ex0 * on1 * nz0)
                else:
                    base = wt * on1 * nz0
                    put((H2, 'SPLITEQ', (dmu,)), base * c11)
                    put((H2, 'INERT', (dmu,)), base * c2)
                    rec(dmu, dv0, wt * (Qa - 1), H2 + (dmu,))

    rec(2 * k, f0init if f0init is not None else 4 * k, 1, ())
    if not alphabet_q and f0init is None:
        assert sum(out.values()) == \
            q ** sum(comp(s) for s in A1all + A0all)
    return out


def s4_mine(q):
    n2 = q * (q - 1) // 2
    d = {'1111': (q - 1) * (q - 2) * (q - 3) * (q - 4) // 24,
         '112': (q - 1) * (q - 2) // 2 * n2,
         '22': n2 * (n2 - 1) // 2,
         '13': (q - 1) * (q ** 3 - q) // 3,
         '4': (q ** 4 - q * q) // 4,
         'D211': (q - 1) * (q - 2) * (q - 3) // 2,
         'D2Q': (q - 1) * n2, 'D22': (q - 1) * (q - 2) // 2,
         'D31': (q - 1) * (q - 2), 'D4': q - 1, 'F': n2}
    assert sum(d.values()) == q ** 3 * (q - 1)
    return d


def my_expected_full(q, N, teeth=None):
    """LAW-key table for a full B-space row (per center)."""
    S4 = s4_mine(q)
    exp = {}

    def put(kk, v):
        if v:
            exp[kk] = exp.get(kk, 0) + v

    ks = [k for k in range(1, N) if 4 * k <= N - 1]
    chains = [()] + [t for r in (1, 2, 3)
                     for t in itertools.combinations(ks, r)]
    for pre in chains:
        wt = (q - 1) ** len(pre)
        kr = pre[-1] if pre else 0
        for u0 in range(4 * kr + 1, N):
            if u0 % 2 == 1:
                s = sum(-(-u0 * (4 - j) // 4) for j in range(4))
                put(('RAM4', pre, (u0,)),
                    wt * (q - 1) * q ** (4 * N - s - 1))
        h = 2 * kr + 1
        while 2 * h <= N - 1:
            vol = q ** (4 * N - 5 * h - 3)
            put(('G2', pre, (h, '11')),
                wt * (q - 1) * (q - 2) // 2 * vol)
            put(('G2', pre, (h, '2')), wt * q * (q - 1) // 2 * vol)
            mE = law_E(q, N, h, integer_only=(teeth == 'LAT'),
                       inert_c=(q * (q - 1) if teeth == 'CEN' else None))
            for (H2, lf, pr), c in mE.items():
                put(('E', pre, h, H2, lf, pr), wt * (q - 1) * c)
            h += 2
        for k in range(kr + 1, N):
            if 4 * k > N - 1:
                break
            vol = q ** (4 * N - 10 * k - 4)
            for tg in ('1111', '112', '22', '13', '4'):
                put(('FULL', pre, (k, tg)), wt * S4[tg] * vol)
            for tg in ('D211', 'D2Q', 'D22', 'D31'):
                put(('SUB', pre, (k, tg)), wt * S4[tg] * vol)
            mF = law_F(q, N, k, alphabet_q=(teeth == 'ALPH'))
            for (H2, lf, pr), c in mF.items():
                put(('F', pre, k, H2, lf, pr), wt * S4['F'] * c)
    return exp


LAW_KINDS = ('RAM4', 'G2', 'FULL', 'SUB', 'E', 'F')


def cmp_tables(fam, rowid, obs, exp, kinds=LAW_KINDS):
    n = 0
    for kk in sorted(set(list(obs) + list(exp)), key=repr):
        if kk[0] not in kinds:
            continue
        n += 1
        if obs.get(kk, 0) != exp.get(kk, 0):
            viol(fam, 'law', '%s %s: obs %s exp %s'
                 % (rowid, kk, obs.get(kk, 0), exp.get(kk, 0)))
    note(fam, n)


def arm_tooth(tooth, q, N, obs, rowid, armed, mode):
    if not armed:
        return
    bad = my_expected_full(q, N, teeth=mode)
    kinds = ('E',) if mode in ('LAT', 'CEN') else ('F',)
    for kk in set(list(obs) + list(bad)):
        if kk[0] in kinds and obs.get(kk, 0) != bad.get(kk, 0):
            FIRE[tooth] += 1
            return
    viol('GH-JSONTIE', 'tooth-dead', '%s on %s' % (tooth, rowid))


# ============ GH-UND / GH-BRACKET closed-form checks ================
def und_E(q, N, h, r, t):
    return (q - 1) ** (r + 1 + t) * q ** (N + h - 1)


def und_F(q, N, k, r, t):
    main = q ** ((k - 1) + 2 * (N // 2) + k)
    extra = (q - 1) * q ** (N + 2 * k - 1) if N % 2 == 0 else 0
    return (q - 1) ** r * (q * q - 1) ** t * (main + extra)


def und_check(rowid, obs, q, N):
    for kk, c in sorted(obs.items(), key=lambda z: repr(z[0])):
        if kk[0] == 'E' and kk[4] == 'UND':
            note('GH-UND')
            w = und_E(q, N, kk[2], len(kk[1]), len(kk[3]))
            if c != w:
                viol('GH-UND', 'E', '%s %s: %d != %d' % (rowid, kk, c, w))
        if kk[0] == 'F' and kk[4] == 'UND':
            note('GH-UND')
            npsi = q * (q - 1) // 2
            w = npsi * und_F(q, N, kk[2], len(kk[1]), len(kk[3]))
            if c != w:
                viol('GH-UND', 'F', '%s %s: %d != %d' % (rowid, kk, c, w))


def bracket_check(rowid, obs, q, N, genre):
    """aggregate over H2 at fixed (pre,entry,leaf,params) ==
    q^{f1*|D_leaf|} x root-history count."""
    groups = {}
    for kk, c in obs.items():
        if kk[0] != genre:
            continue
        groups.setdefault((kk[1], kk[2], kk[4], kk[5]), {})[kk[3]] = c
    f1 = 1 if genre == 'E' else 2
    for (pre, ent, lf, pr), tab in sorted(groups.items(),
                                          key=lambda z: repr(z[0])):
        if genre == 'E':
            lad = [d for d in range(2 * ent + 1, N)]
        else:
            lad = [d for d in range(2 * ent + 1, N) if 2 * d < N]
        if lf in ('RAM', '2SIDED'):
            u = pr[0] if lf == 'RAM' else pr[0] + pr[1]
            D = [d for d in lad if 2 * d < u] if lf == 'RAM' else \
                [d for d in lad if d < pr[0]]
        elif lf in ('SPLITEQ', 'INERT'):
            D = [d for d in lad if d < pr[0]]
        elif lf == 'SPLTAIL':
            D = [d for d in lad if d < pr[0]]
        else:
            D = lad
        note('GH-BRACKET')
        bad = [H for H in tab if not set(H) <= set(D)]
        root = tab.get((), 0)
        want = q ** (f1 * len(D)) * root
        if bad or sum(tab.values()) != want:
            viol('GH-BRACKET', genre,
                 '%s %s %s %s: sum %d != %d (bad %s)'
                 % (rowid, ent, lf, pr, sum(tab.values()), want,
                    bad[:2]))


# ==================== fresh-row machinery ===========================
def absorb_reader_viol(rowid):
    for fam in ('Q22-E', 'Q22-F'):
        if Q.VIOL[fam]:
            viol('GH-FRESH', 'pinned-reader', '%s: %s'
                 % (rowid, Q.VIOL[fam][:2]))
            Q.VIOL[fam][:] = []


def run_consE(kind, q, N, h, sink=None, step=1):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    obs = {}
    tot = 0
    for z, B3, B2, B1, B0 in Q.cons_E_members(R, K, q, N, h):
        key, _ = Q.read22(R, K, q, B3, B2, B1, B0)
        if not (key[0] == 'E' and key[1] == () and key[2] == h):
            viol('GH-FRESH', 'escape', 'consE %s %s %s %s -> %s'
                 % (kind, q, N, h, key))
            continue
        obs[key] = obs.get(key, 0) + 1
        if sink is not None and Q.SIG_KEY(key) is not None \
                and tot % step == 0:
            sink.append((B3, B2, B1, B0, Q.SIG_KEY(key), key))
        tot += 1
    rowid = 'consE %s q=%d N=%d h=%d' % (kind, q, N, h)
    exp = {('E', (), h, H2, lf, pr): (q - 1) * c
           for (H2, lf, pr), c in law_E(q, N, h).items()}
    cmp_tables('GH-FRESH', rowid, obs, exp, kinds=('E',))
    note('GH-FRESH')
    if tot != (q - 1) * q ** (4 * N - 5 * h - 3):
        viol('GH-FRESH', 'volume', rowid)
    for tooth, kw in (('GH-T-LAT', dict(integer_only=True)),
                      ('GH-T-CEN', dict(inert_c=q * (q - 1)))):
        armed = (tooth == 'GH-T-LAT'
                 or any(kk[4] == 'INERT' for kk in obs))
        if armed:
            bad = {('E', (), h, H2, lf, pr): (q - 1) * c
                   for (H2, lf, pr), c in law_E(q, N, h, **kw).items()}
            if bad != obs:
                FIRE[tooth] += 1
            else:
                viol('GH-FRESH', 'tooth-dead', '%s %s' % (tooth, rowid))
    und_check(rowid, obs, q, N)
    bracket_check(rowid, obs, q, N, 'E')
    absorb_reader_viol(rowid)
    say('  [%s] %d members, %d keys (%.1fs)'
        % (rowid, tot, len(obs), time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {repr(k): v for k, v in sorted(obs.items(),
                                                   key=repr)}}, obs


def run_consF(kind, q, N, k, sink=None, step=1):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    obs = {}
    tot = 0
    for psi, B3, B2, B1, B0 in Q.cons_F_members(R, K, q, N, k):
        key, _ = Q.read22(R, K, q, B3, B2, B1, B0)
        if not (key[0] == 'F' and key[1] == () and key[2] == k):
            viol('GH-FRESH', 'escape', 'consF %s %s %s %s -> %s'
                 % (kind, q, N, k, key))
            continue
        obs[key] = obs.get(key, 0) + 1
        if sink is not None and Q.SIG_KEY(key) is not None \
                and tot % step == 0:
            sink.append((B3, B2, B1, B0, Q.SIG_KEY(key), key))
        tot += 1
    rowid = 'consF %s q=%d N=%d k=%d' % (kind, q, N, k)
    npsi = q * (q - 1) // 2
    exp = {('F', (), k, H2, lf, pr): npsi * c
           for (H2, lf, pr), c in law_F(q, N, k).items()}
    cmp_tables('GH-FRESH', rowid, obs, exp, kinds=('F',))
    note('GH-FRESH')
    if tot != npsi * q ** (4 * N - 10 * k - 4):
        viol('GH-FRESH', 'volume', rowid)
    if any(kk[4] in ('SPLITEQ', 'INERT') or kk[3] for kk in obs):
        bad = {('F', (), k, H2, lf, pr): npsi * c
               for (H2, lf, pr), c
               in law_F(q, N, k, alphabet_q=True).items()}
        if bad != obs:
            FIRE['GH-T-ALPH'] += 1
        else:
            viol('GH-FRESH', 'tooth-dead', 'ALPH %s' % rowid)
    und_check(rowid, obs, q, N)
    bracket_check(rowid, obs, q, N, 'F')
    absorb_reader_viol(rowid)
    say('  [%s] %d members, %d keys (%.1fs)'
        % (rowid, tot, len(obs), time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {repr(k): v for k, v in sorted(obs.items(),
                                                   key=repr)}}, obs


def run_full(kind, q, N):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    obs = {}
    tot = 0
    piv = Q.elems_with_floor(R, 1)
    for B3 in piv:
        for B2 in piv:
            for B1 in piv:
                for B0 in piv:
                    key, _ = Q.read22(R, K, q, B3, B2, B1, B0)
                    obs[key] = obs.get(key, 0) + 1
                    tot += 1
    rowid = 'full %s q=%d N=%d' % (kind, q, N)
    note('GH-FRESH')
    if tot != q ** (4 * (N - 1)):
        viol('GH-FRESH', 'partition', rowid)
    cmp_tables('GH-FRESH', rowid, obs, my_expected_full(q, N))
    und_check(rowid, obs, q, N)
    absorb_reader_viol(rowid)
    say('  [%s] %d members, %d keys (%.1fs)'
        % (rowid, tot, len(obs), time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {repr(k): v for k, v in sorted(obs.items(),
                                                   key=repr)}}, obs


def run_pre2(kind, q, N, k1, k2, sink=None, step=256):
    """depth-2 prehistory: floors at k2, inverse-shift twice."""
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    obs = {}
    tot = 0
    for z1 in K.elems():
        if K.is_zero(z1):
            continue
        for z2 in K.elems():
            if K.is_zero(z2):
                continue
            ns1 = W12.rneg(R, R.mul(R.lift(z1), W12.pipow(R, k1)))
            ns2 = W12.rneg(R, R.mul(R.lift(z2), W12.pipow(R, k2)))
            for B3p in Q.elems_with_floor(R, k2 + 1):
                for B2p in Q.elems_with_floor(R, 2 * k2 + 1):
                    for B1p in Q.elems_with_floor(R, 3 * k2 + 1):
                        for B0p in Q.elems_with_floor(R, 4 * k2 + 1):
                            s1 = W12.shift4(R, B3p, B2p, B1p, B0p, ns2)
                            B3, B2, B1, B0 = W12.shift4(R, *s1, ns1)
                            key, _ = Q.read22(R, K, q, B3, B2, B1, B0)
                            if key[1][:2] != (k1, k2):
                                viol('GH-PRE2', 'not-pre2',
                                     '%s -> %s' % ((k1, k2), key))
                                continue
                            obs[key] = obs.get(key, 0) + 1
                            if sink is not None \
                                    and Q.SIG_KEY(key) is not None \
                                    and tot % step == 0:
                                sink.append((B3, B2, B1, B0,
                                             Q.SIG_KEY(key), key))
                            tot += 1
    rowid = 'pre2 %s q=%d N=%d (%d,%d)' % (kind, q, N, k1, k2)
    exp = {kk: v for kk, v in my_expected_full(q, N).items()
           if kk[1] == (k1, k2)}
    obs_law = {kk: v for kk, v in obs.items() if kk[0] in LAW_KINDS}
    cmp_tables('GH-PRE2', rowid, obs_law, exp)
    note('GH-PRE2')
    if tot != (q - 1) ** 2 * q ** (4 * N - 10 * k2 - 4):
        viol('GH-PRE2', 'volume', '%s: %d' % (rowid, tot))
    und_check(rowid, obs_law, q, N)
    absorb_reader_viol(rowid)
    say('  [%s] %d members, %d keys (%.1fs)'
        % (rowid, tot, len(obs), time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {repr(k): v for k, v in sorted(obs.items(),
                                                   key=repr)}}, obs


# ================= GH-REFINE: my own stage walker ===================
def dev22(R, B3, B2, B1, B0, p1, p0):
    """my own division f = phi^2 + A1 phi + A0."""
    q1 = W12.rsub(R, B3, p1)
    q0 = W12.rsub(R, W12.rsub(R, B2, p0), R.mul(q1, p1))
    r1 = W12.rsub(R, W12.rsub(R, B1, R.mul(q1, p0)), R.mul(q0, p1))
    r0 = W12.rsub(R, B0, R.mul(q0, p0))
    return (W12.rsub(R, q1, p1), W12.rsub(R, q0, p0), r1, r0)


def walk_E(R, K, q, h, z, B3, B2, B1, B0, pd_char2=False):
    """my independent E-genre stage walker; verifies the S5 refine
    formulas per event; returns (H2, leaf, params, n_events)."""
    N = R.N
    p1 = W12.rzero(R)
    p0 = W12.rneg(R, R.mul(R.lift(z), W12.pipow(R, h)))
    zinv = K.inv(z)
    two = W12.rint(R, 2)
    H2 = []
    nev = 0
    while True:
        a1, a0, b1, b0 = dev22(R, B3, B2, B1, B0, p1, p0)
        va1, va0 = R.val(a1), R.val(a0)
        vb1, vb0 = R.val(b1), R.val(b0)
        c1s = [x for x in ((2 * va1 + h) if va1 is not None else None,
                           (2 * va0) if va0 is not None else None)
               if x is not None and x < 2 * N]
        c0s = [x for x in ((2 * vb1 + h) if vb1 is not None else None,
                           (2 * vb0) if vb0 is not None else None)
               if x is not None and x < 2 * N]
        dv1 = min(c1s) if c1s else None
        dv0 = min(c0s) if c0s else None
        if dv0 is None:
            if dv1 is not None and dv1 < N:
                return tuple(H2), 'SPLTAIL', (dv1,), nev
            return tuple(H2), 'UND', (), nev
        if dv1 is not None and dv0 > 2 * dv1:
            return tuple(H2), '2SIDED', (dv1, dv0 - dv1), nev
        if dv0 % 2 == 1:
            return tuple(H2), 'RAM', (dv0,), nev
        dmu = dv0 // 2
        S1 = R.res(a1, (dmu - h) // 2) if dmu % 2 == 1 \
            else R.res(a0, dmu // 2)
        S0 = R.res(b0, dmu)
        S0e = K.mul(zinv, S0) if dmu % 2 == 1 else S0
        t, root = W12.quad_type(K, S1, S0e)
        if pd_char2:
            note('GH-PD')
            if (t == '1sq') != K.is_zero(S1):
                viol('GH-PD', 'AS-degeneration',
                     'q=%d h=%d dmu=%d S1zero=%s type=%s'
                     % (q, h, dmu, K.is_zero(S1), t))
        if t == '11':
            return tuple(H2), 'SPLITEQ', (dmu,), nev
        if t == '2':
            return tuple(H2), 'INERT', (dmu,), nev
        s = root
        # my S5 general update (wc, wb) with formula verification
        if dmu % 2 == 1:
            wc = R.mul(R.lift(s), W12.pipow(R, (dmu - h) // 2))
            wb = W12.rzero(R)
        else:
            wc = W12.rzero(R)
            wb = R.mul(R.lift(s), W12.pipow(R, dmu // 2))
        C = R.add(R.mul(wc, wc), R.mul(a1, wc))
        np1 = W12.rsub(R, p1, wc)
        np0 = W12.rsub(R, p0, wb)
        na1 = R.add(a1, R.mul(two, wc))
        na0 = R.add(R.add(a0, R.mul(two, wb)), C)
        nb1 = W12.rsub(
            R, R.add(R.add(b1, R.mul(R.mul(two, wc), wb)),
                     R.add(R.mul(a1, wb), R.mul(a0, wc))),
            R.mul(C, np1))
        nb0 = W12.rsub(R, R.add(b0, R.add(R.mul(wb, wb),
                                          R.mul(a0, wb))),
                       R.mul(C, np0))
        ra1, ra0, rb1, rb0 = dev22(R, B3, B2, B1, B0, np1, np0)
        note('GH-REFINE', 2)
        if not (W12.is_rzero(R, W12.rsub(R, na1, ra1))
                and W12.is_rzero(R, W12.rsub(R, na0, ra0))
                and W12.is_rzero(R, W12.rsub(R, nb1, rb1))
                and W12.is_rzero(R, W12.rsub(R, nb0, rb0))):
            viol('GH-REFINE', 'formula',
                 'E q=%d N=%d h=%d dmu=%d s=%s' % (q, N, h, dmu, s))
        # the pins must die: dv(A1')>dmu, dv(A0')>2dmu
        nva1, nva0 = R.val(ra1), R.val(ra0)
        nvb1, nvb0 = R.val(rb1), R.val(rb0)
        d1n = min([x for x in
                   ((2 * nva1 + h) if nva1 is not None else None,
                    (2 * nva0) if nva0 is not None else None)
                   if x is not None] or [10 ** 9])
        d0n = min([x for x in
                   ((2 * nvb1 + h) if nvb1 is not None else None,
                    (2 * nvb0) if nvb0 is not None else None)
                   if x is not None] or [10 ** 9])
        if not (d1n > dmu and d0n > 2 * dmu):
            viol('GH-REFINE', 'pins-alive',
                 'E q=%d h=%d dmu=%d: %s %s' % (q, h, dmu, d1n, d0n))
        p1, p0 = np1, np0
        H2.append(dmu)
        nev += 1


def walk_F(R, K, q, k, psi, B3, B2, B1, B0):
    N = R.N
    c1, c0 = psi
    F2 = Q.FExt(K, c1, c0)
    p1 = R.mul(R.lift(c1), W12.pipow(R, k))
    p0 = R.mul(R.lift(c0), W12.pipow(R, 2 * k))
    two = W12.rint(R, 2)
    H2 = []
    nev = 0
    while True:
        a1, a0, b1, b0 = dev22(R, B3, B2, B1, B0, p1, p0)
        va1, va0 = R.val(a1), R.val(a0)
        vb1, vb0 = R.val(b1), R.val(b0)
        c1s = [x for x in ((va1 + k) if va1 is not None else None, va0)
               if x is not None and x <= N]
        c0s = [x for x in ((vb1 + k) if vb1 is not None else None, vb0)
               if x is not None and x <= N]
        dv1 = min(c1s) if c1s else None
        dv0 = min(c0s) if c0s else None
        if dv0 is None:
            if dv1 is not None and 2 * dv1 < N:
                return tuple(H2), 'SPLTAIL', (dv1,), nev
            return tuple(H2), 'UND', (), nev
        if dv1 is not None and dv0 > 2 * dv1:
            return tuple(H2), '2SIDED', (dv1, dv0 - dv1), nev
        if dv0 % 2 == 1:
            return tuple(H2), 'RAM', (dv0,), nev
        if dv0 == N:
            return tuple(H2), 'UND', (), nev
        dmu = dv0 // 2
        S1 = (R.res(a1, dmu - k), R.res(a0, dmu))
        S0 = (R.res(b1, dv0 - k), R.res(b0, dv0))
        t, root = W12.quad_type(F2, S1, S0)
        if t == '11':
            return tuple(H2), 'SPLITEQ', (dmu,), nev
        if t == '2':
            return tuple(H2), 'INERT', (dmu,), nev
        sa, sb = root
        wc = R.mul(R.lift(sa), W12.pipow(R, dmu - k))
        wb = R.mul(R.lift(sb), W12.pipow(R, dmu))
        C = R.add(R.mul(wc, wc), R.mul(a1, wc))
        np1 = W12.rsub(R, p1, wc)
        np0 = W12.rsub(R, p0, wb)
        na1 = R.add(a1, R.mul(two, wc))
        na0 = R.add(R.add(a0, R.mul(two, wb)), C)
        nb1 = W12.rsub(
            R, R.add(R.add(b1, R.mul(R.mul(two, wc), wb)),
                     R.add(R.mul(a1, wb), R.mul(a0, wc))),
            R.mul(C, np1))
        nb0 = W12.rsub(R, R.add(b0, R.add(R.mul(wb, wb),
                                          R.mul(a0, wb))),
                       R.mul(C, np0))
        ra1, ra0, rb1, rb0 = dev22(R, B3, B2, B1, B0, np1, np0)
        note('GH-REFINE', 2)
        if not (W12.is_rzero(R, W12.rsub(R, na1, ra1))
                and W12.is_rzero(R, W12.rsub(R, na0, ra0))
                and W12.is_rzero(R, W12.rsub(R, nb1, rb1))
                and W12.is_rzero(R, W12.rsub(R, nb0, rb0))):
            viol('GH-REFINE', 'formula',
                 'F q=%d N=%d k=%d dmu=%d' % (q, N, k, dmu))
        p1, p0 = np1, np0
        H2.append(dmu)
        nev += 1


def run_refine_E(kind, q, N, h):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    nev = 0
    tot = 0
    pd = (q % 2 == 0)
    for z, B3, B2, B1, B0 in Q.cons_E_members(R, K, q, N, h):
        H2, lf, pr, ne = walk_E(R, K, q, h, z, B3, B2, B1, B0,
                                pd_char2=pd)
        key, _ = Q.read22(R, K, q, B3, B2, B1, B0)
        note('GH-REFINE')
        if key != ('E', (), h, H2, lf, pr):
            viol('GH-REFINE', 'walker-vs-reader',
                 '%s vs %s' % (('E', (), h, H2, lf, pr), key))
        nev += ne
        tot += 1
    say('  [refineE %s q=%d N=%d h=%d] %d members, %d refine events '
        '(%.1fs)' % (kind, q, N, h, tot, nev, time.time() - t1))
    return nev


def run_refine_F(kind, q, N, k):
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    nev = 0
    tot = 0
    for psi, B3, B2, B1, B0 in Q.cons_F_members(R, K, q, N, k):
        H2, lf, pr, ne = walk_F(R, K, q, k, psi, B3, B2, B1, B0)
        key, _ = Q.read22(R, K, q, B3, B2, B1, B0)
        note('GH-REFINE')
        if key != ('F', (), k, H2, lf, pr):
            viol('GH-REFINE', 'walker-vs-reader',
                 '%s vs %s' % (('F', (), k, H2, lf, pr), key))
        nev += ne
        tot += 1
    say('  [refineF %s q=%d N=%d k=%d] %d members, %d refine events '
        '(%.1fs)' % (kind, q, N, k, tot, nev, time.time() - t1))
    return nev


# ==================== GH-FEVEN (through GENH4-1F) ===================
def run_feven(kind, q, N, k, f0dv):
    """construct the sub-locus v1(A0) > f0dv via my F development
    relations, read, compare to my conditioned law."""
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    t1 = time.time()
    obs = {}
    tot = 0
    for (c1, c0) in Q.irred_quads(K):
        p1 = R.mul(R.lift(c1), W12.pipow(R, k))
        p0 = R.mul(R.lift(c0), W12.pipow(R, 2 * k))
        p1sq = R.mul(p1, p1)
        for al1 in Q.elems_with_floor(R, k + 1):
            for al0 in Q.elems_with_floor(R, 2 * k + 1):
                for be1 in Q.elems_with_floor(R, f0dv - k):
                    for be0 in Q.elems_with_floor(R, f0dv + 1):
                        B3 = R.add(R.add(p1, p1), al1)
                        B2 = R.add(R.add(p1sq, R.add(p0, p0)),
                                   R.add(R.mul(al1, p1), al0))
                        B1 = R.add(R.add(R.mul(R.mul(p1, p0),
                                                W12.rint(R, 2)),
                                         R.mul(al1, p0)),
                                   R.add(R.mul(al0, p1), be1))
                        B0 = R.add(R.mul(p0, p0),
                                   R.add(R.mul(al0, p0), be0))
                        key, _ = Q.read22(R, K, q, B3, B2, B1, B0)
                        if not (key[0] == 'F' and key[2] == k):
                            viol('GH-FEVEN', 'escape', repr(key))
                            continue
                        obs[key] = obs.get(key, 0) + 1
                        tot += 1
    rowid = 'feven %s q=%d N=%d k=%d f0=%d' % (kind, q, N, k, f0dv)
    npsi = q * (q - 1) // 2
    exp = {('F', (), k, H2, lf, pr): npsi * c
           for (H2, lf, pr), c in law_F(q, N, k, f0init=f0dv).items()}
    cmp_tables('GH-FEVEN', rowid, obs, exp, kinds=('F',))
    if any(kk[4] in ('SPLITEQ', 'INERT') or kk[3] for kk in obs):
        bad = {('F', (), k, H2, lf, pr): npsi * c
               for (H2, lf, pr), c
               in law_F(q, N, k, f0init=f0dv, alphabet_q=True).items()}
        if bad != obs:
            FIRE['GH-T-ALPH'] += 1
        else:
            viol('GH-FEVEN', 'tooth-dead', rowid)
    absorb_reader_viol(rowid)
    say('  [%s] %d members, %d keys (%.1fs)'
        % (rowid, tot, len(obs), time.time() - t1))
    return {'row': rowid, 'members': tot,
            'keys': {repr(kk): v for kk, v in sorted(obs.items(),
                                                     key=repr)}}, obs


# ==================== GH-PD =========================================
def pd_liveness():
    n = 0
    for h in range(1, 16, 2):
        for N in range(2 * h + 1, 41):
            for dmu in range(2 * h + 1, N):
                n += 1
                if dmu % 2 == 1:
                    ok = ((h + 1) // 2 <= (dmu - h) // 2 <= N - 1)
                else:
                    ok = (h + 1 <= dmu // 2 <= N - 1)
                if not ok:
                    viol('GH-PD', 'dead-slot-E',
                         'h=%d N=%d dmu=%d' % (h, N, dmu))
    for k in range(1, 8):
        for N in range(4 * k + 2, 41):
            for dmu in range(2 * k + 1, (N + 1) // 2):
                n += 1
                if not (dmu <= N - 1 and k + 1 <= dmu - k <= N - 1):
                    viol('GH-PD', 'dead-slot-F',
                         'k=%d N=%d dmu=%d' % (k, N, dmu))
    note('GH-PD', n)
    say('  [pd-liveness] %d (h/k,N,dmu) cells scanned' % n)


def pd_cascade(kind, q, N, h):
    """{A1 == 0} sub-locus, the in-vitro P-D exhibit (note S8).
    EQUAL char 2: along the EVEN-dmu ladder the cascade is forced --
    S1 stays dead, every even-dv0 read is '1sq': NO SPLITEQ/INERT key
    may carry an all-even (or empty) H2.  An ODD-dmu refine's CARRY
    C = wc^2 REVIVES A1 (the cocycle escape -- this unit's own smoke
    caught the naive 'no SPLITEQ/INERT ever' claim as too strong,
    twice: mixed char 2 revives via +2w at dv+2e0, equal char via the
    carry; both disclosed in the note S8), after which SPLITEQ/INERT
    are reachable.  Odd q: SPLITEQ/INERT with all-even H2 must EXIST
    (the characteristic separator)."""
    assert q % 2 == 1 or kind == 'Fqt', 'cascade claim is eq-char'
    R = W10.ZpWin(q, N) if kind == 'Zp' else W10.FqtWin(q, N)
    K = R.K
    seen = set()
    tot = 0
    for z in K.elems():
        if K.is_zero(z):
            continue
        w = R.mul(R.lift(z), W12.pipow(R, h))
        two = W12.rint(R, 2)
        for be1 in Q.elems_with_floor(R, (3 * h + 1) // 2):
            for be0 in Q.elems_with_floor(R, 2 * h + 1):
                B3 = W12.rzero(R)
                B2 = W12.rsub(R, W12.rzero(R), R.mul(two, w))
                B1 = be1
                B0 = W12.rsub(R, be0, R.add(R.mul(B2, w),
                                            R.mul(w, w)))
                key, _ = Q.read22(R, K, q, B3, B2, B1, B0)
                if key[0] == 'E':
                    alleven = all(d % 2 == 0 for d in key[3])
                    seen.add((key[4], alleven))
                tot += 1
    rowid = 'pd-cascade %s q=%d N=%d h=%d' % (kind, q, N, h)
    note('GH-PD')
    forced = [s for s in seen
              if s[0] in ('SPLITEQ', 'INERT') and s[1]]
    if q % 2 == 0:
        if forced:
            viol('GH-PD', 'cascade-broken', '%s: %s' % (rowid, forced))
    else:
        if not any(s[0] in ('SPLITEQ', 'INERT') and s[1]
                   for s in seen):
            viol('GH-PD', 'separator-missing',
                 '%s: %s' % (rowid, sorted(seen)))
    say('  [%s] %d members, leaves %s' % (rowid, tot, sorted(seen)))


# ==================== GH-SIGMA (PARI) ===============================
def oracle(p, N, sink, rowid, flip_fram=False):
    t1 = time.time()
    M = p ** N
    jobs = []
    for (B3, B2, B1, B0, sg, key) in sink:
        a3, a2, a1, a0 = B3 % M, B2 % M, B1 % M, B0 % M
        j = 0
        while Q.quartic_disc(a3, a2, a1, a0 + j * M) == 0 and j < 6:
            j += 1
        jobs.append((a3, a2, a1, a0 + j * M, sg, key))
    lines = [W12.GP_FUN]
    for i, (a3, a2, a1, a0, sg, key) in enumerate(jobs):
        lines.append('print("R %d ", sig4(%d,%d,%d,%d,%d))'
                     % (i, a3, a2, a1, a0, p))
    lines.append('quit')
    out = W10.gp_run('\n'.join(lines) + '\n')
    got = {}
    for line in out.splitlines():
        if line.startswith('R '):
            idx, rest = line[2:].split(' ', 1)
            got[int(idx)] = W12.parse_sig(rest)
    note('GH-SIGMA', len(jobs))
    if len(got) != len(jobs):
        viol('GH-SIGMA', 'truncated', '%s: %d/%d'
             % (rowid, len(got), len(jobs)))
    nbad = 0
    fr_c, fr_a = 0, 0
    for i, (a3, a2, a1, a0, sg, key) in enumerate(jobs):
        want = tuple(sorted(sg))
        g = got.get(i)
        if g != want:
            nbad += 1
            if nbad < 6:
                viol('GH-SIGMA', 'sigma', '%s %s: %s != %s'
                     % (rowid, key, g, want))
        if key[0] == 'F' and key[4] == 'RAM':
            fr_a += 1
            if g != ((1, 4),):
                fr_c += 1
    if flip_fram and fr_a:
        if fr_c == fr_a:
            FIRE['GH-T-SIG'] += 1
        else:
            viol('GH-SIGMA', 'tooth-sig-dead', rowid)
    say('  [oracle %s] %d scored, %d bad, F-RAM %d/%d (%.1fs)'
        % (rowid, len(jobs), nbad, fr_c, fr_a, time.time() - t1))
    return {'row': rowid, 'scored': len(jobs), 'bad': nbad}


# ==================== GH-DENS (sympy) ===============================
def density_leg(full_tabs, results, smoke=False):
    import sympy as sp
    sys.path.insert(0, os.path.dirname(HERE))
    import om_density_engine as ENG
    q = sp.Symbol('q', positive=True)
    x = 1 / q

    def simp(e):
        return sp.simplify(sp.together(e))

    def dadd(d, tau, m):
        tau = tuple(sorted(tau))
        d[tau] = d.get(tau, 0) + m

    def dmul(d1, d2):
        out = {}
        for t1, m1 in d1.items():
            for t2, m2 in d2.items():
                dadd(out, tuple(sorted(t1 + t2)), m1 * m2)
        return out

    def dscale(d, c):
        return {t: c * m for t, m in d.items()}

    def dcheck(name, mine, ref):
        note('GH-DENS')
        keys = set(mine) | set(ref)
        for t in keys:
            if sp.simplify(mine.get(t, 0) - ref.get(t, 0)) != 0:
                viol('GH-DENS', name, '%s: %s vs %s'
                     % (t, mine.get(t, 0), ref.get(t, 0)))
                return False
        return True

    # -- block vectors
    nu2 = {((2, 1),): q / (q + 1), ((1, 1), (1, 1)): 1 / (2 * (q + 1)),
           ((1, 2),): 1 / (2 * (q + 1))}
    dcheck('nu2-vs-beta2', nu2, ENG.beta(2))
    Q2 = q ** 2
    nu22 = {((2, 2),): Q2 / (Q2 + 1),
            ((1, 2), (1, 2)): 1 / (2 * (Q2 + 1)),
            ((1, 4),): 1 / (2 * (Q2 + 1))}
    dcheck('nu22-vs-betascaled', nu22, ENG.beta_scaled(2, 2))
    nu3 = ENG.beta(3)

    # -- the stage vectors from the ladder sums (S9.2), closed forms
    def stage_vector(Qs, taus, censusC2=None):
        y = 1 / Qs
        g3 = 1 - y ** 3
        ram_n = (Qs - 1) * y / g3
        spq_n = (Qs - 1) * (Qs - 2) / (2 * Qs) * y ** 2 / g3
        c2 = censusC2 if censusC2 is not None else sp.Rational(1, 2)
        ine_n = (Qs - 1) * c2 * y ** 2 / g3
        ref_n = (Qs - 1) / Qs * y ** 2 / g3
        two_n = 1 - simp(ram_n + spq_n + ine_n + ref_n)
        # independent direct 2SIDED evaluation (odd + even legs)
        two_dir = (Qs - 1) * (y / (1 - y ** 2) - y / g3) \
            + (Qs - 1) * (y ** 2 / (1 - y ** 2) - y ** 2 / g3)
        note('GH-DENS')
        if censusC2 is None and sp.simplify(two_n - two_dir) != 0:
            viol('GH-DENS', '2sided-node', str(Qs))
        den = 1 - ref_n
        return {taus[0]: simp(ram_n / den),
                taus[1]: simp((two_n + spq_n) / den),
                taus[2]: simp(ine_n / den)}

    muE = stage_vector(q, (((4, 1),), ((2, 1), (2, 1)), ((2, 2),)))
    note('GH-DENS')
    if not dcheck('muE-fractions',
                  {t: muE[t] for t in muE},
                  {((4, 1),): q / (q + 1),
                   ((2, 1), (2, 1)): 1 / (2 * (q + 1)),
                   ((2, 2),): 1 / (2 * (q + 1))}):
        pass
    muF = stage_vector(Q2, (((2, 2),), ((1, 2), (1, 2)), ((1, 4),)))
    dcheck('muF-vs-nu22', muF, nu22)
    # tooth GH-T-DENS: corrupted E-INERT census must break
    muE_bad = stage_vector(q, (((4, 1),), ((2, 1), (2, 1)),
                               ((2, 2),)), censusC2=sp.Integer(1))
    if sp.simplify(sum(muE_bad.values()) - 1) != 0 or \
            sp.simplify(muE_bad[((2, 2),)] - muE[((2, 2),)]) != 0:
        FIRE['GH-T-DENS'] += 1
    else:
        viol('GH-DENS', 'tooth-dead', 'GH-T-DENS')

    # -- nu4: the depth-0 family table (note S9.3), symbolic sums
    T10 = x ** 10 / (1 - x ** 10)
    fam = []          # (mass, dist or 'SELF')

    def one(tau):
        return {tuple(sorted(tau)): sp.Integer(1)}

    # A1 RAM4
    fam.append(((q - 1) * (x + x ** 6) / (1 - x ** 10),
                one(((4, 1),))))
    # A2 G2
    g2m = x ** 4 / (1 - x ** 10)
    fam.append((g2m * (q - 1) * (q - 2) / 2, one(((2, 1), (2, 1)))))
    fam.append((g2m * q * (q - 1) / 2, one(((2, 2),))))
    fam.append((g2m * (q - 1), muE))
    # A3 FULL
    n2c = q * (q - 1) / 2
    s4sym = {'1111': (q - 1) * (q - 2) * (q - 3) * (q - 4) / 24,
             '112': (q - 1) * (q - 2) / 2 * n2c,
             '22': n2c * (n2c - 1) / 2,
             '13': (q - 1) * (q ** 3 - q) / 3,
             '4': (q ** 4 - q ** 2) / 4,
             'D211': (q - 1) * (q - 2) * (q - 3) / 2,
             'D2Q': (q - 1) * n2c, 'D22': (q - 1) * (q - 2) / 2,
             'D31': (q - 1) * (q - 2), 'D4': q - 1, 'F': n2c}
    note('GH-DENS')
    if sp.simplify(sum(s4sym.values()) - q ** 3 * (q - 1)) != 0:
        viol('GH-DENS', 's4-census', 'sum != q^3(q-1)')
    outc = {'1111': one(((1, 1),) * 4),
            '112': one(((1, 1), (1, 1), (1, 2))),
            '22': one(((1, 2), (1, 2))), '13': one(((1, 1), (1, 3))),
            '4': one(((1, 4),)),
            'D211': dmul(nu2, one(((1, 1), (1, 1)))),
            'D2Q': dmul(nu2, one(((1, 2),))), 'D22': dmul(nu2, nu2),
            'D31': dmul(nu3, one(((1, 1),))), 'F': muF}
    for tg, S in s4sym.items():
        if tg == 'D4':
            continue
        fam.append((T10 * S, outc[tg]))
    p_pre = (q - 1) * T10

    # side outcome distributions (per drop parity), censuses inline
    side2_odd = ((q - 1), one(((2, 1),)))
    side2_even = [((q - 1) * (q - 2) / 2, one(((1, 1), (1, 1)))),
                  (q * (q - 1) / 2, one(((1, 2),))), ((q - 1), nu2)]
    side3_n3 = ((q - 1), one(((3, 1),)))       # 3 nmid drop
    side3_div = [((q - 1) * (q - 2) * (q - 3) / 6,
                  one(((1, 1),) * 3)),
                 ((q - 1) * q * (q - 1) / 2, one(((1, 1), (1, 2)))),
                 ((q ** 3 - q) / 3, one(((1, 3),))),
                 ((q - 1) * (q - 2), dmul(nu2, one(((1, 1),)))),
                 ((q - 1), nu3)]

    g1 = 1 - x
    g3 = 1 - x ** 3
    g6 = 1 - x ** 6
    g10 = 1 - x ** 10

    # family B: V={0,2,4}; c right drop, D left drop > c.
    # closed forms per parity case (note S9.3): total exponents
    # 10i+{9,8,13,15} for (oo,oe,eo,ee), all x q^2 / (1-x^3)(1-x^10).
    for cpar, Dpar, e0 in (('odd', 'odd', 9), ('odd', 'even', 8),
                           ('even', 'odd', 13), ('even', 'even', 15)):
        for (cS, cdist) in ([side2_odd] if cpar == 'odd'
                            else side2_even):
            for (DS, Ddist) in ([side2_odd] if Dpar == 'odd'
                                else side2_even):
                mass = q ** 2 * cS * DS * x ** e0 / (g3 * g10)
                fam.append((mass, dmul(cdist, Ddist)))
    # family C: V={0,1,4}: u1=3t+rho, d1>=t+1
    #   rho=0 (t>=1, L=4): x^11 ; rho=1: q^2 x^5 ; rho=2: q^2 x^8
    for (S3, d3) in side3_div:
        fam.append(((q - 1) * S3 * x ** 11 / (g1 * g10),
                    dmul(one(((1, 1),)), d3)))
    for e0 in (5, 8):
        fam.append(((q - 1) * side3_n3[0] * q ** 2 * x ** e0
                    / (g1 * g10),
                    dmul(one(((1, 1),)), side3_n3[1])))
    # family D: V={0,3,4}: a>=1, D3=3t+rho>=3a+1
    #   rho=0: x^16 ; rho=1: q^2 x^13 ; rho=2: q^2 x^15
    for (S3, d3) in side3_div:
        fam.append(((q - 1) * S3 * x ** 16 / (g6 * g10),
                    dmul(d3, one(((1, 1),)))))
    for e0 in (13, 15):
        fam.append(((q - 1) * side3_n3[0] * q ** 2 * x ** e0
                    / (g6 * g10),
                    dmul(side3_n3[1], one(((1, 1),)))))
    # family E: V={0,1,2,4}: c odd: q x^8 ; c even: x^14
    for cpar, coeff in (('odd', q * x ** 8), ('even', x ** 14)):
        for (cS, cdist) in ([side2_odd] if cpar == 'odd'
                            else side2_even):
            fam.append(((q - 1) ** 2 * cS * coeff / (g1 * g3 * g10),
                        dmul(one(((1, 1), (1, 1))), cdist)))
    # family F: V={0,1,3,4}: c2 odd: q x^14 ; c2 even: x^17
    for cpar, coeff in (('odd', q * x ** 14), ('even', x ** 17)):
        for (cS, cdist) in ([side2_odd] if cpar == 'odd'
                            else side2_even):
            fam.append(((q - 1) ** 2 * cS * coeff / (g1 * g6 * g10),
                        dmul(one(((1, 1), (1, 1))), cdist)))
    # family G: V={0,2,3,4}: c odd: q x^18 ; c even: x^19
    for cpar, coeff in (('odd', q * x ** 18), ('even', x ** 19)):
        for (cS, cdist) in ([side2_odd] if cpar == 'odd'
                            else side2_even):
            fam.append(((q - 1) ** 2 * cS * coeff / (g3 * g6 * g10),
                        dmul(cdist, one(((1, 1), (1, 1))))))
    # family H: four simple sides
    mH = (q - 1) ** 4 * (x ** 10 / (1 - x ** 10)) \
        * (x ** 6 / (1 - x ** 6)) * (x ** 3 / (1 - x ** 3)) \
        * (x / (1 - x))
    fam.append((mH, one(((1, 1),) * 4)))

    # partition of unity
    total = simp(sum(m for m, _ in fam) + p_pre)
    note('GH-DENS')
    if sp.simplify(total - 1) != 0:
        viol('GH-DENS', 'partition-of-unity', str(simp(total)))
    # assemble nu4
    nu4 = {}
    for m, d in fam:
        for tau, w in d.items():
            dadd(nu4, tau, m * w)
    nu4 = {tau: simp(v / (1 - p_pre)) for tau, v in nu4.items()}
    dcheck('nu4-vs-beta4', nu4, ENG.beta(4))

    # corrupted-census nu4 must break the beta4 tie (tooth support)
    # (already fired above via muE_bad)

    # -- level-0 assembly: the eleven R_tau
    n2f = (q ** 2 - q) / 2
    n3f = (q ** 3 - q) / 3
    n4f = (q ** 4 - q ** 2) / 4
    C = sp.binomial
    shapes = [
        (C(q, 4), one(((1, 1),) * 4)),
        (C(q, 2) * n2f, one(((1, 1), (1, 1), (1, 2)))),
        (n2f * (n2f - 1) / 2, one(((1, 2), (1, 2)))),
        (q * n3f, one(((1, 1), (1, 3)))),
        (n4f, one(((1, 4),))),
        (q * C(q - 1, 2), dmul(nu2, one(((1, 1), (1, 1))))),
        (q * n2f, dmul(nu2, one(((1, 2),)))),
        (C(q, 2), dmul(nu2, nu2)),
        (q * (q - 1), dmul(nu3, one(((1, 1),)))),
        (q, nu4),
        (n2f, nu22),
    ]
    note('GH-DENS')
    if sp.simplify(sum(c for c, _ in shapes) - q ** 4) != 0:
        viol('GH-DENS', 'level0-census', 'sum != q^4')
    Rtau = {}
    for c, d in shapes:
        for tau, w in d.items():
            dadd(Rtau, tau, c / q ** 4 * w)
    Rtau = {tau: simp(v) for tau, v in Rtau.items()}
    note('GH-DENS')
    if sp.simplify(sum(Rtau.values()) - 1) != 0:
        viol('GH-DENS', 'sum-Rtau', 'Sigma != 1')
    say('  == THE ELEVEN QUARTIC DENSITIES R_tau(q) ==')
    for tau in sorted(Rtau):
        say('    R_%s = %s' % (tau, sp.factor(Rtau[tau])))
    for qv in (2, 3, 5):
        vals = {tau: sp.nsimplify(Rtau[tau].subs(q, qv))
                for tau in Rtau}
        note('GH-DENS')
        if sum(vals.values()) != 1:
            viol('GH-DENS', 'anchor-sum', 'q=%d' % qv)
        say('    q=%d: %s' % (qv, {str(tt): str(vv) for tt, vv
                                   in sorted(vals.items())}))
    results['Rtau'] = {str(tau): str(sp.factor(v))
                       for tau, v in sorted(Rtau.items())}

    # -- partial-sum sandwich on full B-space rows
    G2SIG = {'11': ((2, 1), (2, 1)), '2': ((2, 2),)}
    FULLSIG = {'1111': ((1, 1),) * 4, '112': ((1, 1), (1, 1), (1, 2)),
               '22': ((1, 2), (1, 2)), '13': ((1, 1), (1, 3)),
               '4': ((1, 4),)}
    for rowid, (qv, N, obs) in sorted(full_tabs.items()):
        res = {}
        tot = 0
        for kk, c in obs.items():
            tot += c
            sg = None
            if kk[0] == 'RAM4':
                sg = ((4, 1),)
            elif kk[0] == 'G2':
                sg = G2SIG.get(kk[2][1])
            elif kk[0] == 'FULL':
                sg = FULLSIG.get(kk[2][1])
            elif kk[0] in ('E', 'F'):
                sg = Q.SIG_KEY(kk)
                sg = tuple(sorted(sg)) if sg else None
            if sg:
                res[tuple(sorted(sg))] = \
                    res.get(tuple(sorted(sg)), 0) + c
        unres = tot - sum(res.values())
        blk = Fraction(qv) ** (4 * (N - 1))
        for tau in set(list(nu4) + list(res)):
            note('GH-DENS')
            nval = sp.nsimplify(nu4[tau].subs(q, qv)) \
                if tau in nu4 else sp.Integer(0)
            nf = sp.fraction(sp.together(nval))
            target = Fraction(int(nf[0]), int(nf[1])) * blk
            lo = Fraction(res.get(tau, 0))
            if not (lo <= target <= lo + unres):
                viol('GH-DENS', 'sandwich',
                     '%s %s: %s <= %s <= %s fails'
                     % (rowid, tau, lo, target, lo + unres))
    say('  [GH-DENS] symbolic leg complete')


# ============================ main ==================================
def main(smoke=False):
    t0 = time.time()
    say('GENH4 battery -- %s' % ('SMOKE' if smoke else 'FULL ROSTER'))
    for fn, want in PINS.items():
        with open(os.path.join(HERE, fn), 'rb') as fh:
            md5 = hashlib.md5(fh.read()).hexdigest()
        note('GH-PIN')
        if md5 != want:
            viol('GH-PIN', 'moved', '%s %s != %s' % (fn, md5, want))
        say('  pin %s = %s' % (fn, md5))

    results = {'rows': [], 'oracle': [], 'smoke': smoke}
    full_tabs = {}   # rowid -> (q, N, obs) for the density sandwich

    # ---- GH-JSONTIE: the committed QSCOUT22 roster
    with open(os.path.join(HERE, 'qscout22_results.json')) as fh:
        JR = json.load(fh)
    for rec in JR['rows']:
        rid = rec['row']
        obs = {ast.literal_eval(k): v for k, v in rec['keys'].items()}
        parts = rid.split()
        qv = int(parts[2].split('=')[1])
        N = int(parts[3].split('=')[1])
        if rid.startswith('full'):
            cmp_tables('GH-JSONTIE', rid, obs, my_expected_full(qv, N))
            full_tabs[rid] = (qv, N, obs)
            hasE = any(kk[0] == 'E' for kk in obs)
            hasI = any(kk[0] == 'E' and kk[4] == 'INERT' for kk in obs)
            hasFd = any(kk[0] == 'F' and (kk[4] in ('SPLITEQ', 'INERT')
                                          or kk[3]) for kk in obs)
            arm_tooth('GH-T-LAT', qv, N, obs, rid, hasE, 'LAT')
            arm_tooth('GH-T-CEN', qv, N, obs, rid, hasI, 'CEN')
            arm_tooth('GH-T-ALPH', qv, N, obs, rid, hasFd, 'ALPH')
        elif rid.startswith('consE'):
            h = int(parts[4].split('=')[1])
            exp = {('E', (), h, H2, lf, pr): (qv - 1) * c
                   for (H2, lf, pr), c in law_E(qv, N, h).items()}
            cmp_tables('GH-JSONTIE', rid, obs, exp, kinds=('E',))
            bracket_check(rid, obs, qv, N, 'E')
            badL = {('E', (), h, H2, lf, pr): (qv - 1) * c
                    for (H2, lf, pr), c
                    in law_E(qv, N, h, integer_only=True).items()}
            if badL != obs:
                FIRE['GH-T-LAT'] += 1
            if any(kk[4] == 'INERT' for kk in obs):
                badC = {('E', (), h, H2, lf, pr): (qv - 1) * c
                        for (H2, lf, pr), c
                        in law_E(qv, N, h,
                                 inert_c=qv * (qv - 1)).items()}
                if badC != obs:
                    FIRE['GH-T-CEN'] += 1
        elif rid.startswith('consF'):
            k = int(parts[4].split('=')[1])
            npsi = qv * (qv - 1) // 2
            exp = {('F', (), k, H2, lf, pr): npsi * c
                   for (H2, lf, pr), c in law_F(qv, N, k).items()}
            cmp_tables('GH-JSONTIE', rid, obs, exp, kinds=('F',))
            bracket_check(rid, obs, qv, N, 'F')
            if any(kk[4] in ('SPLITEQ', 'INERT') or kk[3]
                   for kk in obs):
                badA = {('F', (), k, H2, lf, pr): npsi * c
                        for (H2, lf, pr), c
                        in law_F(qv, N, k, alphabet_q=True).items()}
                if badA != obs:
                    FIRE['GH-T-ALPH'] += 1
        elif rid.startswith('pre'):
            k1 = int(parts[4].split('=')[1])
            exp = {kk: v for kk, v in my_expected_full(qv, N).items()
                   if kk[1] and kk[1][0] == k1}
            obs_law = {kk: v for kk, v in obs.items()
                       if kk[0] in LAW_KINDS}
            cmp_tables('GH-JSONTIE', rid, obs_law, exp)
        und_check(rid, {kk: v for kk, v in obs.items()
                        if kk[0] in ('E', 'F')}, qv, N)
    say('  [GH-JSONTIE] all committed rows checked')

    # ---- fresh rows
    sinks = {}
    if smoke:
        CONSE = [('Zp', 7, 3, 1)]
        CONSF = [('Zp', 2, 9, 2)]
        FULLR = []
        PRE2 = []
        FEVEN = []
        REFE = [('Zp', 2, 6, 1)]
        REFF = []
    else:
        CONSE = [('Zp', 7, 3, 1), ('Fqt', 5, 4, 1), ('Fqt', 3, 5, 1),
                 ('Zp', 2, 11, 5)]
        CONSF = [('Zp', 7, 5, 1), ('Zp', 2, 9, 2)]
        FULLR = [('Fqt', 5, 3)]
        PRE2 = [('Zp', 2, 11, 1, 2)]
        FEVEN = [('Zp', 3, 7, 1, 5)]
        REFE = [('Zp', 2, 6, 1), ('Fqt', 2, 6, 1)]
        REFF = [('Zp', 2, 7, 1)]

    STEPS = {('Zp', 7, 3, 1): 8, ('Zp', 2, 11, 5): 16,
             ('Zp', 7, 5, 1): 512, ('Zp', 2, 9, 2): 4}
    for (kind, qv, N, h) in CONSE:
        sink = [] if kind == 'Zp' else None
        rec, obs = run_consE(kind, qv, N, h, sink=sink,
                             step=STEPS.get((kind, qv, N, h), 64))
        results['rows'].append(rec)
        if sink:
            sinks['consE Zp q=%d N=%d h=%d' % (qv, N, h)] = \
                (qv, N, sink)
    for (kind, qv, N, k) in CONSF:
        sink = [] if kind == 'Zp' else None
        rec, obs = run_consF(kind, qv, N, k, sink=sink,
                             step=STEPS.get((kind, qv, N, k), 64))
        results['rows'].append(rec)
        if sink:
            sinks['consF Zp q=%d N=%d k=%d' % (qv, N, k)] = \
                (qv, N, sink)
    for (kind, qv, N) in FULLR:
        rec, obs = run_full(kind, qv, N)
        results['rows'].append(rec)
        full_tabs[rec['row']] = (qv, N, obs)
    for (kind, qv, N, k1, k2) in PRE2:
        sink = []
        rec, obs = run_pre2(kind, qv, N, k1, k2, sink=sink, step=256)
        results['rows'].append(rec)
        if sink:
            sinks[rec['row']] = (qv, N, sink)
    for (kind, qv, N, k, f0) in FEVEN:
        rec, obs = run_feven(kind, qv, N, k, f0)
        results['rows'].append(rec)

    # ---- GH-REFINE
    for (kind, qv, N, h) in REFE:
        run_refine_E(kind, qv, N, h)
    for (kind, qv, N, k) in REFF:
        run_refine_F(kind, qv, N, k)

    # ---- GH-PD
    pd_liveness()
    if not smoke:
        pd_cascade('Fqt', 2, 7, 1)
        pd_cascade('Zp', 3, 5, 1)
    else:
        pd_cascade('Fqt', 2, 6, 1)

    # ---- GH-SIGMA
    for rowid, (qv, N, sink) in sorted(sinks.items()):
        if not sink:
            continue
        hasF = any(key[0] == 'F' and key[4] == 'RAM'
                   for (_, _, _, _, _, key) in sink)
        results['oracle'].append(
            oracle(qv, N, sink, rowid, flip_fram=hasF))

    # ---- GH-DENS
    density_leg(full_tabs, results, smoke=smoke)

    # ---- verdict
    say('')
    say('== FAMILY TOTALS ==')
    red = False
    for f in FAMILIES:
        say('  %-11s checks %-8d violations %d'
            % (f, NCHK[f], len(VIOL[f])))
        if VIOL[f]:
            red = True
    say('== TEETH ==')
    for tt in TEETH:
        say('  %-11s fired %d' % (tt, FIRE[tt]))
        if FIRE[tt] == 0:
            red = True
            say('  RED: tooth %s never fired' % tt)
    say('== %s (%.1fs) ==' % ('RED' if red else 'GREEN',
                              time.time() - t0))
    results['families'] = {f: [NCHK[f], len(VIOL[f]), VIOL[f][:20]]
                           for f in FAMILIES}
    results['teeth'] = dict(FIRE)
    results['verdict'] = 'RED' if red else 'GREEN'
    results['elapsed_s'] = round(time.time() - t0, 1)
    suff = '_smoke' if smoke else ''
    with open(os.path.join(HERE, 'genh4_checks_results%s.json' % suff),
              'w') as fh:
        json.dump(results, fh, indent=1, default=repr)
    with open(os.path.join(HERE, 'genh4_checks_output%s.txt' % suff),
              'w') as fh:
        fh.write('\n'.join(LOG) + '\n')
    return 0 if not red else 1


if __name__ == '__main__':
    sys.exit(main(smoke='--smoke' in sys.argv))
