#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""grt_jb_printwalk.py -- POST-SEAL SUPPLEMENTARY print-key tree walker.

Repair round r1 of lean/notes/openmath/GRTJB_PROOF_2026-08-08.md, written
against JB-PE1 finding G-1 (report lean/notes/openmath/GRTJB_passPE1_report.md,
commit 85a8dc9).  THIS SCRIPT IS NOT PART OF THE SEALED JB BATTERY: the sealed
runner grt_jb_checks.py is byte-frozen through the acceptance arc and is NOT
imported here at all (in particular its fresh_divmod is never called).  This
file carries its own mini two-commit seal: the predictions below are committed
BEFORE any full run, and the verdict is appended to the note's r1 block from
the committed artifacts grt_jb_printwalk_output.txt / _results.json.

WHAT G-1 SAID.  The sealed runner's JB-TREE leg advertises the tree identity
"by the harness key AND by the print-side key", but the print-key leg runs
only under `byteeq` (equal tuples), where it re-executes the SAME pure
function on the SAME arguments -- it cannot fail unless the harness leg does,
and off the byte-equal set nothing print-side is checked.  This script closes
that hole with a genuinely print-keyed instrument.

WHAT IS PRINT-SIDE HERE (the independence claim, stated precisely).
  * every KEY is a print key: phi_1..phi_{m+2} from grt_weld_probe.GmnLeg's
    own _thm_phir/construct recursion (the sealed GMN transcription);
  * the CORRECTION DIGITS are extracted from the print chain itself, as the
    phi_{i+1}-adic development digits of phi_{i+2} ((ID-(i+1)) read print-side)
    -- no psi/eps/realize/harness-lift call anywhere in the walk;
  * the MULTIPLICAND is print-side too: Chat_m^cls := phi_{m+2} -
    phi_{m+1}^{e_m} (the g_m = 1 WELL-DEF form at print keys);
  * the DIVISOR is the print key phi_{m+1}, and the division is computed by
    THIS FILE's own Horner/synthetic implementation my_divmod (structurally
    different from both the engine's divmod_monic and the sealed runner's
    fresh_divmod), each call self-checked by reassembly + degree bound;
  * the level scope is computed print-side (g_m = f^cls_{m+1} = 1; T-scope
    from d0 = f^cls_0 and the print e's), with NO shared-key (qcap) cut, so
    the walker may cover levels the sealed battery skipped.
  HARNESS INPUTS, disclosed: the sample polynomials f (grt_ja_checks
  .sample_pool, i.e. the same rows the sealed battery scored), the degree
  filter deg f < deg phi_{m+1}, and -- in the cross-frame family only, where
  it is the point -- the harness keys Phi_j and harness Chat_m.

========================= PREREGISTERED FAMILIES ==============================
PW-ID     the print (ID-(i+1)) structure read off the print chain alone: the
          phi_{i+1}-adic development of phi_{i+2} has digit 1 at abscissa
          P_i = e^cls_{i+1}*f^cls_{i+1}, digits only at abscissas
          e^cls_{i+1}*k with k < f^cls_{i+1} below it, and nothing off that
          grid.                                        PREDICT: 0 violations.
PW-WALK   the fresh E1-priority walk on the initial cells of f*Chat^cls
          terminates under the step cap and every R-leaf is reduced
          (j_l <= P_l - 1 for all l < m).               PREDICT: 0.
PW-REASM  exact signed reassembly in O[x]:
          sum(R-leaves) + sum(exit cofactors)*phi_{m+1} == f*Chat^cls.
                                                        PREDICT: 0.
PW-DIV    (sum R-leaves, sum exits) == my_divmod(f*Chat^cls, phi_{m+1}), and
          the same pair == the engine's PolyO.divmod_monic (third leg).
                                                        PREDICT: 0.
PW-XFRAME cross-frame (LEG B): on rows whose print key chain is byte-equal
          through m, a SECOND print-keyed walk is run on the harness
          multiplicand f*Chat^har (the sealed theorem's own object) and its
          (sum leaves, sum exits) is compared with my_divmod(f*Chat^har,
          Phi_m^har).  This is the sealed JB-TREE claim recomputed with a
          print-keyed tree whose correction digits come from DIVIDING PRINT
          KEYS instead of from realize(eps^{-1} psi) -- a decorrelated code
          path, not a re-execution.  PREDICT: 0 mismatches, firing on 67 of
          the 79 walks (the sealed JSON's `byteeq`-true rows).  Where the
          chain diverges leg B is NOT claimed (different divisor) and only
          the census is reported.
COVERAGE  predicted from the committed sealed artifact
          grt_jb_checks_results.json (its per-row `tree` block): 79 print-key
          walks (LEG A) on the same rows (16-tower roster 69 + QO leg 2 + d0
          leg 8), of which 12 sit at junctions where the sealed runner's
          `byteeq` is FALSE (T3A, T3C, T3D, T3E at m = 2, three walks each)
          -- i.e. 12 walks that the sealed battery's print-key leg never ran.
                                            PREDICT: 79 total / 12 unequal.
DISAGREEMENT DISCIPLINE: any failure is printed in full (family, tag, level,
the two polynomials' coefficient lists truncated to 40 entries) and counted;
nothing is suppressed, and a nonzero exit code is returned.

BUILD-PHASE SMOKE DISCLOSURE (pre-seal, honest): before this file was
committed a reduced smoke (T2A + T3A only, same code path) ran to shake down
runner-local code, ALL FIVE FAMILIES GREEN on 9 LEG-A walks (3 of them at a
byte-unequal junction, T3A m = 2) with leg B firing on 6 of the 9 and
agreeing on all 6.  It found ONE design defect, fixed before
this seal: the first draft gated the cross-frame family on
(chain byte-equal through m) AND (Chat^cls == Chat^har), which fired on ZERO
smoke rows -- a vacuous check, exactly the disease G-1 reports.  Leg B above
is the re-gated family (a second print-keyed walk on the harness
multiplicand, fired by chain byte-equality alone).  No law-side prediction was
tuned on the smoke: PW-ID/WALK/REASM/DIV are the note's own displayed
identities and the COVERAGE numbers are read off the committed sealed JSON.
Deterministic; exact arithmetic; no RNG.
"""
import sys, os, json, time, collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL
import grt_weld_probe as GWP
import grt_ja_checks as GJA

VIOL = []
COUNTS = collections.defaultdict(int)
RES = {'rows': {}, 'families': {}, 'coverage': {}, 'violations': []}


def note(fam, n=1):
    COUNTS[fam] += n


def viol(fam, tag, msg):
    VIOL.append((fam, tag, str(msg)))
    print('  VIOLATION [%s] %s: %s' % (fam, tag, str(msg)[:400]))


# ---------------------------------------------------- own polynomial layer
def my_divmod(R, f, Phi):
    """OWN division by the monic Phi, Horner/synthetic from the top with a
    running remainder window (structurally distinct from the elimination
    loops in PolyO.divmod_monic and in the sealed runner's fresh_divmod).
    Self-checked by reassembly + degree bound."""
    d = len(Phi) - 1
    assert d >= 1 and Phi[-1] == R.one(), 'divisor not monic'
    acc = []                       # running remainder, low..high
    Q = [R.zero()]*max(1, len(f))
    for i in range(len(f) - 1, -1, -1):
        acc = [f[i]] + acc         # acc <- acc*x + f_i
        if len(acc) == d + 1:
            a = acc[d]
            if not R.is_zero(a):
                Q[i] = a
                acc = [R.add(acc[j], R.neg(R.mul(a, Phi[j])))
                       for j in range(d + 1)]
            acc = acc[:d]
    def trim(L):
        L = list(L)
        while L and R.is_zero(L[-1]):
            L.pop()
        return tuple(L)
    return trim(Q), trim(acc)


def cdivmod(P, R, f, Phi, tag, fam='PW-DIV'):
    """my_divmod + the reassembly/degree certificate (so the verdict does not
    rest on the implementation)."""
    Q, rem = my_divmod(R, f, Phi)
    if tuple(P.add(rem, P.mul(Q, Phi))) != tuple(P.canon(list(f))):
        viol(fam, tag, 'my_divmod certificate FAILS (reassembly)')
    if rem and len(rem) - 1 >= len(Phi) - 1:
        viol(fam, tag, 'my_divmod certificate FAILS (degree bound)')
    return Q, rem


def my_dev(P, R, f, Phi, tag):
    out = []
    cur = tuple(P.canon(list(f)))
    while cur:
        cur, rem = cdivmod(P, R, cur, Phi, tag)
        out.append(rem)
    return out


def w0(R, f):
    vs = [R.val(c) for c in f if not R.is_zero(c)]
    return min(vs) if vs else None


def pi_div(R, a, w):
    if w == 0 or R.is_zero(a):
        return a
    if isinstance(R, ITL.Zp):
        q, r = divmod(a, R.p**w)
        assert r == 0, 'pi_div not exact'
        return q
    assert all(c == 0 for c in a[:w]), 'pi_div not exact (Fpt)'
    return tuple(a[w:])


def poly_pi_div(R, f, w):
    return tuple(pi_div(R, c, w) for c in f)


# ------------------------------------------------- print-side tree machinery
def pcells(T, G, poly, lvl, tag):
    """reduced-cell decomposition against the PRINT keys phi_1..phi_lvl:
    list of (b, jvec), jvec of length lvl, b of degree < d0."""
    P, R = T.P, T.R
    if not poly:
        return []
    if lvl == 0:
        return [(tuple(poly), ())]
    out = []
    for j, A in enumerate(my_dev(P, R, poly, tuple(G.phi[lvl]), tag)):
        if A:
            for b, jv in pcells(T, G, A, lvl - 1, tag):
                out.append((b, jv + (j,)))
    return out


def plnorm(T, G, b, c, tag):
    """L-NORM at the print bottom key phi_1: b*c = pi^w lift(bbar cbar)
    + pi^{w+1} Xhat + pi^w phi_1 Yhat.  Exactness self-checked."""
    P, R = T.P, T.R
    w = w0(R, b) + w0(R, c)
    prod = tuple(P.mul(b, c))
    Phat = poly_pi_div(R, prod, w)
    Y0, r = cdivmod(P, R, Phat, tuple(G.phi[1]), tag, fam='PW-WALK')
    Lbar = P.canon([R.liftk(R.res(cc, 0)) for cc in r])
    if not Lbar:
        viol('PW-WALK', tag, 'L-NORM L-child vanished (L-NORM(a) breach)')
    Xhat = poly_pi_div(R, P.sub(r, Lbar), 1)
    Lp = tuple(P.scal(R.pi_pow(w), Lbar))
    Xp = tuple(P.scal(R.pi_pow(w + 1), Xhat))
    Yp = tuple(P.scal(R.pi_pow(w), Y0))
    recon = P.add(P.add(Lp, Xp), P.mul(Yp, G.phi[1]))
    if tuple(recon) != prod:
        viol('PW-WALK', tag, 'L-NORM split not exact')
    return [(t, pp, 1 if t == 'Y' else 0)
            for t, pp in (('L', Lp), ('X', Xp), ('Y', Yp)) if pp]


def print_corr(T, G, m, tag):
    """print-side correction digits + the (ID) structure check (PW-ID).
    Returns {i: [(k, cells of C_k^{(i)})]} for i = 0..m-1."""
    P, R = T.P, T.R
    corr = {}
    for i in range(m):
        e_, f_ = G.e[i + 1], G.f[i + 1]
        Pi = e_*f_
        note('PW-ID')
        dv = my_dev(P, R, tuple(G.phi[i + 2]), tuple(G.phi[i + 1]), tag)
        rows = []
        for j, A in enumerate(dv):
            if not A:
                continue
            if j == Pi:
                if tuple(A) != (R.one(),):
                    viol('PW-ID', tag, 'top digit != 1 at i=%d' % i)
                continue
            if j % e_ == 0 and j//e_ < f_:
                rows.append((j//e_, tuple(A)))
                continue
            viol('PW-ID', tag, 'print key dev OFF-GRID at i=%d j=%d' % (i, j))
        if len(dv) - 1 != Pi:
            viol('PW-ID', tag, 'print key dev top abscissa %d != P_%d = %d'
                 % (len(dv) - 1, i, Pi))
        corr[i] = [(k, pcells(T, G, cd, i, tag)) for k, cd in rows]
    return corr


def pcellpoly(T, G, b, j):
    out = tuple(b)
    for l, jl in enumerate(j):
        out = tuple(T.P.mul(out, T.P.pow(G.phi[l + 1], jl)))
    return out


def psigned_sum(T, G, items):
    acc = ()
    for sgn, b, j in items:
        cp = pcellpoly(T, G, b, j)
        acc = tuple(T.P.add(acc, cp if sgn > 0 else T.P.neg(cp)))
    return acc


def pwalk(T, G, m, f, Chat, Pl, corr, tag, cap=60000):
    """FRESH E1-priority walk at PRINT keys on the initial cells of f*Chat."""
    stack = []
    for bx, jx in pcells(T, G, f, m, tag):
        for cD, jD in pcells(T, G, Chat, m, tag):
            jj = tuple(jx[l] + jD[l] for l in range(m))
            for typ, bb, dj0 in plnorm(T, G, bx, cD, tag):
                j2 = (jj[0] + dj0,) + jj[1:] if dj0 else jj
                stack.append((1, bb, j2))
    leaves, exits = [], []
    steps = 0
    while stack:
        steps += 1
        if steps > cap:
            return None
        sgn, b, j = stack.pop()
        i = next((l for l in range(m) if j[l] >= Pl[l]), None)
        if i is None:
            leaves.append((sgn, b, j))
            continue
        if i <= m - 2:
            j2 = list(j); j2[i] -= Pl[i]; j2[i + 1] += 1
            stack.append((sgn, b, tuple(j2)))
        else:
            j2 = list(j); j2[m - 1] -= Pl[m - 1]
            exits.append((sgn, b, tuple(j2)))
        for k, dcells in corr[i]:
            for cd, ad in dcells:
                for typ, bb, dj0 in plnorm(T, G, b, cd, tag):
                    j2 = list(j)
                    j2[i] -= Pl[i] - G.e[i + 1]*k
                    for l in range(i):
                        j2[l] += ad[l]
                    j2[0] += dj0
                    stack.append((-sgn, bb, tuple(j2)))
    return leaves, exits


def print_elig(T, G):
    """print-side eligible reduction levels: g_m = f^cls_{m+1} = 1 and
    T-scope (d0 = 1 or all lower print e >= 2).  No qcap cut."""
    out = []
    for m in range(1, T.n + 1):
        if G.f[m + 1] != 1:
            continue
        if not (G.f[0] == 1 or all(G.e[i + 1] >= 2 for i in range(m))):
            continue
        out.append(m)
    return out


def run_tower(T, G, tag):
    P, R = T.P, T.R
    pool = GJA.sample_pool(T, small=False)
    for m in print_elig(T, G):
        key = tuple(G.phi[m + 1])
        Pl = [G.e[l + 1]*G.f[l + 1] for l in range(m)]
        corr = print_corr(T, G, m, tag)
        Chat = tuple(P.sub(G.phi[m + 2], P.pow(key, G.e[m + 1])))
        dK = len(key) - 1
        fpool = [f for f in pool if f and P.deg(f) < dK][:3]
        if not fpool:
            continue
        chain_eq = all(tuple(T.Phi[j]) == tuple(G.phi[j + 1])
                       for j in range(0, m + 1))
        top_eq = (tuple(G.phi[m + 1]) == tuple(T.Phi[m]))
        Phi_up = tuple(T.Phi[m + 1]) if m + 1 <= T.n else tuple(GWP.top_lift(T))
        Chat_har = tuple(P.sub(Phi_up, P.pow(tuple(T.Phi[m]), T.e[m])))
        row = {'walks': 0, 'chain_eq': bool(chain_eq), 'top_eq': bool(top_eq),
               'chat_eq': bool(Chat == Chat_har), 'xframe_rows': 0,
               'xframe_agree': 0, 'unequal_walks': 0, 'frames_differ': 0}
        for f in fpool:      # LEG A: print-internal (f * Chat^cls)
            note('PW-WALK')
            wk = pwalk(T, G, m, f, Chat, Pl, corr, tag)
            if wk is None:
                viol('PW-WALK', tag, 'print walk cap hit at m=%d' % m)
                continue
            leaves, exits = wk
            for sgn, b, j in leaves:
                if any(j[l] > Pl[l] - 1 for l in range(m)):
                    viol('PW-WALK', tag, 'non-reduced R-leaf m=%d j=%s'
                         % (m, j))
                    break
            fC = tuple(P.mul(f, Chat))
            R0 = psigned_sum(T, G, leaves)
            Qp = psigned_sum(T, G, exits)
            note('PW-REASM')
            if tuple(P.add(R0, P.mul(Qp, key))) != fC:
                viol('PW-REASM', tag,
                     'print reassembly FAILS m=%d: tree %s vs f*Chat %s'
                     % (m, list(P.add(R0, P.mul(Qp, key)))[:40], list(fC)[:40]))
                continue
            note('PW-DIV')
            Qm, Rm = cdivmod(P, R, fC, key, tag)
            if (R0, Qp) != (Rm, Qm):
                viol('PW-DIV', tag,
                     'print tree != own print-key division m=%d: '
                     'R tree %s vs div %s ; Q tree %s vs div %s'
                     % (m, list(R0)[:40], list(Rm)[:40],
                        list(Qp)[:40], list(Qm)[:40]))
            Qe, Re = P.divmod_monic(fC, key)
            if (tuple(Re), tuple(Qe)) != (Rm, Qm):
                viol('PW-DIV', tag,
                     'own division != engine divmod_monic m=%d' % m)
            row['walks'] += 1
            if not top_eq:
                row['unequal_walks'] += 1
                COUNTS['PW-UNEQUAL-WALKS'] += 1
            # LEG B (cross-frame): a SECOND print-keyed walk, on the harness
            # multiplicand, compared with the harness-key division.  Claimed
            # only where the key chain is byte-equal through m.
            if not chain_eq:
                row['frames_differ'] += 1
                COUNTS['PW-CHAIN-DIVERGENT'] += 1
                continue
            note('PW-XFRAME')
            row['xframe_rows'] += 1
            wkh = pwalk(T, G, m, f, Chat_har, Pl, corr, tag)
            if wkh is None:
                viol('PW-XFRAME', tag, 'cross-frame walk cap hit at m=%d' % m)
                continue
            lh, xh = wkh
            R0h = psigned_sum(T, G, lh)
            Qph = psigned_sum(T, G, xh)
            fCh = tuple(P.mul(f, Chat_har))
            Qh, Rh = cdivmod(P, R, fCh, tuple(T.Phi[m]), tag,
                             fam='PW-XFRAME')
            if (R0h, Qph) != (Rh, Qh):
                viol('PW-XFRAME', tag,
                     'byte-equal row: PRINT-keyed tree != harness-key '
                     'division m=%d: R tree %s vs div %s ; Q tree %s vs '
                     'div %s' % (m, list(R0h)[:40], list(Rh)[:40],
                                 list(Qph)[:40], list(Qh)[:40]))
                continue
            if tuple(P.add(R0h, P.mul(Qph, tuple(T.Phi[m])))) != fCh:
                viol('PW-XFRAME', tag,
                     'cross-frame reassembly FAILS m=%d' % m)
                continue
            row['xframe_agree'] += 1
            COUNTS['PW-XFRAME-AGREE'] += 1
        RES['rows']['%s|m=%d' % (tag, m)] = row


def main(smoke=False):
    t0 = time.time()
    print('grt_jb_printwalk.py -- POST-SEAL print-key tree walker%s'
          % (' [SMOKE]' if smoke else ''))
    roster = GWP.TOWERS if not smoke else \
        [s for s in GWP.TOWERS if s['id'] in ('T2A', 'T3A')]
    for spec in roster:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        T = ITL.build_tower(spec)
        G = GWP.gmn_from_tower(T)
        run_tower(T, G, tag)
        print('  [%6.1fs] %-18s done' % (time.time() - t0, tag))
    if not smoke:
        for name, p, fc in GWP.QO_SHAPES:
            tag = 'QO:%s/Q%d' % (name, p)
            leg, levels, status = GWP.qo_extract(ITL.Zp(p), fc)
            if status != 'complete':
                print('  QO %s: extraction %s (skipped)' % (tag, status))
                continue
            reads = [(e, h, len(psi) - 1) for (e, h, psi) in levels]
            psi_specs = [[('RAW', c) for c in psi] for (e, h, psi) in levels]
            try:
                T = GWP.SpecTower(tag, ITL.Zp(p), 1, [0, 1], reads, psi_specs)
                G = GWP.gmn_from_tower(T)
            except AssertionError as ex:
                print('  QO %s: tower build failed (%s)' % (tag, ex))
                continue
            run_tower(T, G, tag)
        print('  [%6.1fs] QO leg done' % (time.time() - t0))
        for spec in GJA.D0_SPECS:
            tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
            T = ITL.build_tower(spec)
            G = GWP.gmn_from_tower(T)
            run_tower(T, G, tag)
        print('  [%6.1fs] d0>=2 leg done' % (time.time() - t0))
    print()
    print('=' * 78)
    print('PREDICTED vs OBSERVED (violations; samples in parentheses)')
    print('=' * 78)
    fams = [('PW-ID', 'print (ID-(i+1)) structure from the print chain', '0'),
            ('PW-WALK', 'print E1 walk terminates + leaves reduced', '0'),
            ('PW-REASM', 'signed reassembly == f*Chat^cls', '0'),
            ('PW-DIV', 'tree == own print-key division (+ engine)', '0'),
            ('PW-XFRAME', 'byte-eq rows: print tree == harness division',
             '0')]
    all_ok = True
    for fam, desc, pred in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        if obs:
            all_ok = False
        print('%-10s %-45s pred %-3s obs %5d (%6d)  %s'
              % (fam, desc, pred, obs, COUNTS.get(fam, 0),
                 'GREEN' if obs == 0 else 'RED'))
    print('-' * 78)
    tw = sum(r['walks'] for r in RES['rows'].values())
    uw = COUNTS.get('PW-UNEQUAL-WALKS', 0)
    print('COVERAGE: LEG-A print-key walks %d (predicted 79) | at '
          'byte-UNEQUAL junctions %d (predicted 12)' % (tw, uw))
    print('CROSS-FRAME (LEG B): fired %d (predicted 67), agreeing %d | '
          'chain-divergent LEG-A walks, leg B not claimed: %d'
          % (COUNTS.get('PW-XFRAME', 0), COUNTS.get('PW-XFRAME-AGREE', 0),
             COUNTS.get('PW-CHAIN-DIVERGENT', 0)))
    print('rows (tag|m -> walks/unequal/xframe): %d' % len(RES['rows']))
    for k in sorted(RES['rows']):
        r = RES['rows'][k]
        print('   %-26s walks %d  top_eq %-5s chain_eq %-5s chat_eq %-5s '
              'xframe %d/%d  differ %d'
              % (k, r['walks'], r['top_eq'], r['chain_eq'], r['chat_eq'],
                 r['xframe_agree'], r['xframe_rows'], r['frames_differ']))
    if VIOL:
        print('%d VIOLATIONS (all, up to 60):' % len(VIOL))
        for v in VIOL[:60]:
            print('  ', v)
    RES['families'] = {fam: {'pred': pred,
                             'obs': sum(1 for v in VIOL if v[0] == fam),
                             'samples': COUNTS.get(fam, 0)}
                       for fam, desc, pred in fams}
    RES['coverage'] = {'walks': tw, 'unequal_walks': uw,
                       'xframe_fired': COUNTS.get('PW-XFRAME', 0),
                       'xframe_agree': COUNTS.get('PW-XFRAME-AGREE', 0),
                       'chain_divergent_walks':
                           COUNTS.get('PW-CHAIN-DIVERGENT', 0)}
    RES['violations'] = [list(v) for v in VIOL]
    RES['elapsed_s'] = round(time.time() - t0, 1)
    if not smoke:
        out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           'grt_jb_printwalk_results.json')
        with open(out, 'w') as fh:
            json.dump(RES, fh, indent=1, default=repr)
        print('JSON: %s' % out)
    print('TOTAL samples %d  elapsed %.1fs'
          % (sum(COUNTS.values()), time.time() - t0))
    print()
    print('PRINT-WALK VERDICT: %s'
          % ('ALL GREEN (the print-key tree identity holds at print keys, '
             'including off the byte-equal set)' if all_ok
             else 'RED -- disagreement displayed above'))
    return 0 if all_ok else 1


if __name__ == '__main__':
    sys.exit(main(smoke=('--smoke' in sys.argv)))
