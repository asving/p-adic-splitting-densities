#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""grt_jb_printwalk2.py -- r2 GATE REPAIR for the cross-frame family PW-XFRAME.

Repair round r2 of lean/notes/openmath/GRTJB_PROOF_2026-08-08.md, written
against JB-PE2 finding G2-2 (report lean/notes/openmath/GRTJB_passPE2_report.md,
committed by that pass).  NOT part of the sealed JB battery: the sealed runner
grt_jb_checks.py is byte-frozen and is NOT imported here (its fresh_divmod is
never called).  This file carries its own mini two-commit seal: the predictions
below are committed BEFORE any full run, and the verdict is transcribed into
the note's r2 block from the committed artifacts grt_jb_printwalk2_output.txt /
_results.json.

WHAT G2-2 SAID.  The r1 walker grt_jb_printwalk.py gates its cross-frame family
PW-XFRAME on `chain_eq` ALONE.  `chain_eq` = (Phi_j == phi_{j+1} for all
j <= m) already forces the leg-B divisor Phi_m to be byte-equal to the print key
phi_{m+1}; so on the subset where the multiplicand is byte-equal too
(`chat_eq`, i.e. Chat^cls == Chat^har) leg B calls the SAME pure functions on
BYTE-IDENTICAL arguments as leg A's PW-DIV -- it cannot fail unless PW-DIV
already did.  That is exactly the defect JB-PE1's G-1 charged against the
SEALED runner's print-key leg, reproduced inside the instrument written to
repair it.  The r1 walker's own smoke disclosure shows the author saw the
failure mode and RE-GATED by DROPPING the `chat_eq` conjunct, where the fix was
to NEGATE it.  On the committed r1 artifacts 27 of the 72 PW-XFRAME walks
(9 rows) are such degenerate re-executions.

WHAT THIS SCRIPT DOES (and does not).  It is a GATE REPAIR, not a decorrelated
second instrument: it deliberately REUSES the byte-frozen r1 walker's own
print-side machinery by import (PW.print_corr / PW.pcells / PW.plnorm /
PW.pwalk / PW.my_divmod / PW.cdivmod / PW.print_elig -- the r1 file is imported
and NEVER edited, its mini-seal md5 unchanged), so that the ONLY difference
from the r1 run is the gate and the census.  Consequently it inherits the r1
walker's independence properties (print keys from GmnLeg's own recursion,
correction digits by DIVIDING print keys, own Horner division certified per
call) and adds nothing to them; what it adds is honesty about which walks carry
cross-frame content.

========================= PREREGISTERED FAMILIES ==============================
Numbers below are READ OFF the committed r1 artifact grt_jb_printwalk_results
.json (its 28-row `rows` block, fields chain_eq / chat_eq / walks) -- they are
NOT blind predictions; the blind content is the VERDICT on each family.

PW2-XFRAME  the HONEST cross-frame family: gate chain_eq AND NOT chat_eq.  A
            second print-keyed walk is run on the HARNESS multiplicand
            f*Chat^har and compared with PW.my_divmod(f*Chat^har, Phi_m^har)
            (certified by reassembly + degree bound), on rows where the
            multiplicand genuinely DIFFERS between the frames.  Each sample
            additionally carries a NON-DEGENERACY certificate:
            f*Chat^cls != f*Chat^har as byte tuples.
                    PREDICT: 0 mismatches, 0 certificate failures,
                             firing on 45 walks over 15 rows.
PW2-DEGEN   the degenerate complement: gate chain_eq AND chat_eq.  Here NO
            comparison is re-run (re-running it is the disease).  Instead the
            DEGENERACY is CERTIFIED mechanically: the whole leg-B argument
            tuple is byte-identical to leg A's, i.e.
            f*Chat^har == f*Chat^cls AND Phi_m^har == phi_{m+1}^cls, so
            PW.pwalk and PW.my_divmod are being called on identical inputs and
            agreement is a fact about pure functions, not evidence.
                    PREDICT: 27 walks over 9 rows, 0 certificate failures.
PW2-NOCLAIM census only: chain-divergent rows (NOT chain_eq), where leg B is
            not claimable at all (the harness divisor is a different
            polynomial).  These are the byte-UNEQUAL junctions that carry the
            r1 walker's leg-A value.
                    PREDICT: 12 walks over 4 rows.
PW2-RECON   reconciliation against the committed r1 JSON: for every (tag|m) row
            this run must reproduce the r1 walker's own chain_eq / chat_eq /
            walks entries exactly, and 45 + 27 + 12 = 84 = the r1 leg-A walk
            count.  Any mismatch is DISPLAYED row by row.
                    PREDICT: 28 rows reconciled, 0 disagreements.

DISAGREEMENT DISCIPLINE: any failure is printed in full (family, tag, level,
both coefficient lists truncated to 40 entries) and counted; nothing is
suppressed and the exit code is nonzero.  Deterministic, exact arithmetic,
no RNG.  No smoke run preceded this file (its code path is the r1 walker's,
already exercised); the only new code is the gate, the certificates and the
reconciliation.
"""
import sys, os, json, time, collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL
import grt_weld_probe as GWP
import grt_ja_checks as GJA
import grt_jb_printwalk as PW          # byte-frozen r1 walker: imported, never edited

VIOL = []
COUNTS = collections.defaultdict(int)
RES = {'rows': {}, 'families': {}, 'coverage': {}, 'violations': []}


def note(fam, n=1):
    COUNTS[fam] += n


def viol(fam, tag, msg):
    VIOL.append((fam, tag, str(msg)))
    print('  VIOLATION [%s] %s: %s' % (fam, tag, str(msg)[:400]))


def run_tower2(T, G, tag):
    P, R = T.P, T.R
    pool = GJA.sample_pool(T, small=False)
    for m in PW.print_elig(T, G):
        key = tuple(G.phi[m + 1])
        Pl = [G.e[l + 1]*G.f[l + 1] for l in range(m)]
        corr = PW.print_corr(T, G, m, tag)
        Chat = tuple(P.sub(G.phi[m + 2], P.pow(key, G.e[m + 1])))
        dK = len(key) - 1
        fpool = [f for f in pool if f and P.deg(f) < dK][:3]
        if not fpool:
            continue
        chain_eq = all(tuple(T.Phi[j]) == tuple(G.phi[j + 1])
                       for j in range(0, m + 1))
        Phi_up = tuple(T.Phi[m + 1]) if m + 1 <= T.n else tuple(GWP.top_lift(T))
        Chat_har = tuple(P.sub(Phi_up, P.pow(tuple(T.Phi[m]), T.e[m])))
        div_har = tuple(T.Phi[m])
        chat_eq = (Chat == Chat_har)
        row = {'walks': 0, 'chain_eq': bool(chain_eq), 'chat_eq': bool(chat_eq),
               'xframe': 0, 'xframe_agree': 0, 'degen': 0, 'noclaim': 0}
        for f in fpool:
            row['walks'] += 1
            fC = tuple(P.mul(f, Chat))
            fCh = tuple(P.mul(f, Chat_har))
            if not chain_eq:
                row['noclaim'] += 1
                COUNTS['PW2-NOCLAIM'] += 1
                continue
            if chat_eq:
                # DEGENERATE: certify byte-identity of the argument tuple; do
                # NOT re-run the comparison (that re-execution is the defect).
                note('PW2-DEGEN')
                row['degen'] += 1
                if fCh != fC:
                    viol('PW2-DEGEN', tag,
                         'chat_eq row but f*Chat^har != f*Chat^cls at m=%d: '
                         '%s vs %s' % (m, list(fCh)[:40], list(fC)[:40]))
                if div_har != key:
                    viol('PW2-DEGEN', tag,
                         'chain_eq row but Phi_m != phi_{m+1} at m=%d: '
                         '%s vs %s' % (m, list(div_har)[:40], list(key)[:40]))
                continue
            # HONEST CROSS-FRAME: the multiplicand differs between frames.
            note('PW2-XFRAME')
            row['xframe'] += 1
            if fCh == fC:
                viol('PW2-XFRAME', tag,
                     'non-degeneracy certificate FAILS at m=%d: '
                     'f*Chat^har == f*Chat^cls on a chat_eq=False row' % m)
            nv = len(PW.VIOL)
            wkh = PW.pwalk(T, G, m, f, Chat_har, Pl, corr, tag)
            if wkh is None:
                viol('PW2-XFRAME', tag, 'cross-frame walk cap hit at m=%d' % m)
                continue
            lh, xh = wkh
            R0h = PW.psigned_sum(T, G, lh)
            Qph = PW.psigned_sum(T, G, xh)
            Qh, Rh = PW.cdivmod(P, R, fCh, div_har, tag, fam='PW2-XFRAME')
            if len(PW.VIOL) != nv:
                for v in PW.VIOL[nv:]:
                    viol('PW2-XFRAME', tag,
                         'inherited certificate failure from the r1 '
                         'machinery: %s' % (v,))
            if (R0h, Qph) != (Rh, Qh):
                viol('PW2-XFRAME', tag,
                     'PRINT-keyed tree != harness-key division on a '
                     'GENUINELY cross-frame row m=%d: R tree %s vs div %s ; '
                     'Q tree %s vs div %s'
                     % (m, list(R0h)[:40], list(Rh)[:40],
                        list(Qph)[:40], list(Qh)[:40]))
                continue
            if tuple(P.add(R0h, P.mul(Qph, div_har))) != fCh:
                viol('PW2-XFRAME', tag,
                     'cross-frame reassembly FAILS m=%d' % m)
                continue
            row['xframe_agree'] += 1
            COUNTS['PW2-XFRAME-AGREE'] += 1
        RES['rows']['%s|m=%d' % (tag, m)] = row


def reconcile():
    """PW2-RECON: every row must match the committed r1 walker JSON."""
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        'grt_jb_printwalk_results.json')
    with open(path) as fh:
        J = json.load(fh)
    old = J['rows']
    keys = sorted(set(old) | set(RES['rows']))
    for k in keys:
        note('PW2-RECON')
        if k not in old or k not in RES['rows']:
            viol('PW2-RECON', k, 'row present in only one instrument')
            continue
        a, b = old[k], RES['rows'][k]
        for fld in ('chain_eq', 'chat_eq'):
            if bool(a[fld]) != bool(b[fld]):
                viol('PW2-RECON', k, '%s: r1 %s vs r2 %s'
                     % (fld, a[fld], b[fld]))
        if a['walks'] != b['walks']:
            viol('PW2-RECON', k, 'walks: r1 %d vs r2 %d'
                 % (a['walks'], b['walks']))
        # the r1 leg-B fire count must be our degen + xframe on this row
        if a['xframe_rows'] != b['degen'] + b['xframe']:
            viol('PW2-RECON', k, 'r1 xframe_rows %d != degen %d + xframe %d'
                 % (a['xframe_rows'], b['degen'], b['xframe']))
    tot = sum(r['walks'] for r in RES['rows'].values())
    oldtot = sum(r['walks'] for r in old.values())
    if tot != oldtot:
        viol('PW2-RECON', 'TOTAL', 'r2 walks %d != r1 leg-A walks %d'
             % (tot, oldtot))
    return oldtot


def main():
    t0 = time.time()
    print('grt_jb_printwalk2.py -- r2 cross-frame GATE REPAIR '
          '(chain_eq AND NOT chat_eq)')
    for spec in GWP.TOWERS:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        T = ITL.build_tower(spec)
        G = GWP.gmn_from_tower(T)
        run_tower2(T, G, tag)
        print('  [%6.1fs] %-18s done' % (time.time() - t0, tag))
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
        run_tower2(T, G, tag)
    print('  [%6.1fs] QO leg done' % (time.time() - t0))
    for spec in GJA.D0_SPECS:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        T = ITL.build_tower(spec)
        G = GWP.gmn_from_tower(T)
        run_tower2(T, G, tag)
    print('  [%6.1fs] d0>=2 leg done' % (time.time() - t0))
    oldtot = reconcile()
    if PW.VIOL:
        # any certificate breach raised inside the imported r1 machinery
        for v in PW.VIOL:
            if not any(v[2] in w[2] for w in VIOL):
                viol('PW2-INHERITED', v[1], 'r1-machinery breach: %s' % (v,))

    print()
    print('=' * 78)
    print('PREDICTED vs OBSERVED (violations; samples in parentheses)')
    print('=' * 78)
    fams = [('PW2-XFRAME', 'HONEST cross-frame: chain_eq AND NOT chat_eq',
             '0', 45),
            ('PW2-DEGEN', 'degeneracy certified (no re-run): chain&chat',
             '0', 27),
            ('PW2-RECON', 'row-for-row reconciliation vs the r1 JSON',
             '0', 28)]
    all_ok = not VIOL          # ANY violation, in any family, turns this RED
    for fam, desc, pred, psamp in fams:
        obs = sum(1 for v in VIOL if v[0] == fam)
        got = COUNTS.get(fam, 0)
        print('%-11s %-44s pred %-3s obs %5d (%5d samples, predicted %d)  %s'
              % (fam, desc, pred, obs, got, psamp,
                 'GREEN' if obs == 0 else 'RED'))
        if got != psamp:
            print('             SAMPLE-COUNT MIS-PREDICTION: %d vs %d'
                  % (got, psamp))
    print('-' * 78)
    xf = COUNTS.get('PW2-XFRAME', 0)
    dg = COUNTS.get('PW2-DEGEN', 0)
    nc = COUNTS.get('PW2-NOCLAIM', 0)
    print('CENSUS: cross-frame walks %d (predicted 45, agreed %d) | '
          'DEGENERATE re-execution walks %d (predicted 27) | '
          'chain-divergent, leg B not claimable %d (predicted 12)'
          % (xf, COUNTS.get('PW2-XFRAME-AGREE', 0), dg, nc))
    print('        total walks considered %d (r1 leg-A walks %d) | rows %d'
          % (xf + dg + nc, oldtot, len(RES['rows'])))
    print('        r1 PW-XFRAME advertised 72 samples = %d cross-frame + '
          '%d degenerate' % (xf, dg))
    rowsx = [k for k in sorted(RES['rows']) if RES['rows'][k]['xframe']]
    rowsd = [k for k in sorted(RES['rows']) if RES['rows'][k]['degen']]
    rowsn = [k for k in sorted(RES['rows']) if RES['rows'][k]['noclaim']]
    print('CROSS-FRAME rows (%d):' % len(rowsx))
    for k in rowsx:
        print('   %-26s xframe %d/%d'
              % (k, RES['rows'][k]['xframe_agree'], RES['rows'][k]['xframe']))
    print('DEGENERATE rows (%d) -- VACUOUS for cross-frame purposes:'
          % len(rowsd))
    for k in rowsd:
        print('   %-26s degen %d' % (k, RES['rows'][k]['degen']))
    print('CHAIN-DIVERGENT rows (%d) -- leg B not claimable:' % len(rowsn))
    for k in rowsn:
        print('   %-26s walks %d' % (k, RES['rows'][k]['noclaim']))
    if VIOL:
        print('%d VIOLATIONS (all, up to 60):' % len(VIOL))
        for v in VIOL[:60]:
            print('  ', v)
    RES['families'] = {fam: {'pred': pred, 'pred_samples': psamp,
                             'obs': sum(1 for v in VIOL if v[0] == fam),
                             'samples': COUNTS.get(fam, 0)}
                       for fam, desc, pred, psamp in fams}
    RES['coverage'] = {'xframe_walks': xf, 'xframe_agree':
                       COUNTS.get('PW2-XFRAME-AGREE', 0),
                       'degenerate_walks': dg, 'noclaim_walks': nc,
                       'r1_legA_walks': oldtot, 'rows': len(RES['rows'])}
    RES['violations'] = [list(v) for v in VIOL]
    RES['elapsed_s'] = round(time.time() - t0, 1)
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'grt_jb_printwalk2_results.json')
    with open(out, 'w') as fh:
        json.dump(RES, fh, indent=1, default=repr)
    print('JSON: %s' % out)
    print('TOTAL samples %d (law families only: PW2-XFRAME %d + PW2-DEGEN %d '
          '+ PW2-RECON %d)  elapsed %.1fs'
          % (xf + dg + COUNTS.get('PW2-RECON', 0), xf, dg,
             COUNTS.get('PW2-RECON', 0), time.time() - t0))
    print()
    print('PRINT-WALK2 VERDICT: %s'
          % ('GREEN -- the print-keyed tree == the harness-key division on '
             'the NON-DEGENERATE cross-frame walks, and the degenerate '
             'complement is certified vacuous' if all_ok
             else 'RED -- disagreement displayed above'))
    return 0 if all_ok else 1


if __name__ == '__main__':
    sys.exit(main())
