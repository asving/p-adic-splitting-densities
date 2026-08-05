#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""grt_jb_r1_levelcensus.py -- POST-SEAL r1 evidence, NOT a sealed prediction.

Repair round r1 of lean/notes/openmath/GRTJB_PROOF_2026-08-08.md, written
against JB-PE1 finding F1 (report GRTJB_passPE1_report.md, commit 85a8dc9).

WHY: the sealed runner grt_jb_checks.py aggregates the JB-CREAD boundary
census PER TOWER only, so its JSON cannot say at which reduction level m each
boundary row sits -- and F1 turns on exactly that (the note's r0 grade surface
claimed (VD-m) unconditional at m <= 2).  This script re-keys the census by
(level, side, reason) by importing the sealed runner VERBATIM (read-only; the
runner and its JSON are byte-untouched) and replaying `jb_cread`'s own control
flow -- same towers, same sample pool, same eligibility and qcap cuts, same
`vd_eval` -- while recording m and the failure side instead of only the
aggregate.  It also cross-checks its own totals against the committed sealed
JSON's per-row `cread` block.  No prediction is registered: this is a
RECOMPUTATION of a disclosed census at finer resolution.

Output: grt_jb_r1_levelcensus_output.txt (tee'd by caller).
Deterministic; exact arithmetic; no RNG.
"""
import sys, os, json, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import iterlawn_pe_reimpl as ITL
import grt_weld_probe as GWP
import grt_ja_checks as GJA
import grt_jb_checks as JB               # sealed runner, imported verbatim

CEN = collections.Counter()


def cread_levelkeyed(T, G, tag, m, fpool, cm):
    """jb_cread's control flow, level- and reason-keyed."""
    K = T.K[m]
    e, h = T.e[m - 1], T.h[m - 1]
    gam1 = T.gam[m + 1]
    Chat = JB.chat_of(T, m)
    Phim = tuple(T.Phi[m])
    for f in fpool:
        fC = tuple(T.P.mul(f, Chat))
        _, Rr = JB.fresh_divmod(T.R, fC, Phim)
        if not Rr:
            CEN[(tag, m, 'R=0')] += 1
            continue
        vdf, rho_f, _, v = JB.vd_eval(T, G, m, f)
        if K.is_zero(v):
            CEN[(tag, m, 'v=0')] += 1
            continue
        if vdf is None:
            CEN[(tag, m, 'BOUNDARY f SCOPE-OUT')] += 1
            continue
        if not vdf:
            CEN[(tag, m, 'BOUNDARY f EVAL-FALSE')] += 1
            continue
        vdR, rho_R, _, _ = JB.vd_eval(T, G, m, Rr)
        if vdR is None:
            CEN[(tag, m, 'BOUNDARY R SCOPE-OUT')] += 1
            continue
        if not vdR:
            CEN[(tag, m, 'BOUNDARY R EVAL-FALSE')] += 1
            continue
        CEN[(tag, m, 'SCORED')] += 1


def main():
    print('grt_jb_r1_levelcensus.py -- level-keyed JB-CREAD boundary census')
    for spec in GWP.TOWERS:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        T = ITL.build_tower(spec)
        G = GWP.gmn_from_tower(T)
        pool = GJA.sample_pool(T, small=False)
        for m in JB.elig_ms(T):
            if m > JB.qcap_of(T, G):
                continue
            dPh = len(T.Phi[m]) - 1
            fpool = [f for f in pool if f and T.P.deg(f) < dPh][:3]
            if not fpool:
                continue
            cm = JB.jb_cm(T, tag, m, fam='JB-CM')
            if cm is None:
                print('  c_m unavailable at %s m=%d (skipped)' % (tag, m))
                continue
            cread_levelkeyed(T, G, tag, m, fpool, cm)
    bylevel = collections.Counter()
    for (tag, m, kind), n in CEN.items():
        bylevel[(m, 'BOUNDARY' if kind.startswith('BOUNDARY') else kind)] += n
    print()
    print('=== per (level, class) over the 16-tower roster ===')
    for k in sorted(bylevel):
        print('  m=%d  %-10s %4d' % (k[0], k[1], bylevel[k]))
    print('=== boundary rows: tower / level / reason ===')
    per = collections.Counter()
    for (tag, m, kind), n in sorted(CEN.items()):
        if kind.startswith('BOUNDARY'):
            print('  %-18s m=%d  %-26s %d' % (tag, m, kind[9:], n))
            per[(tag.split(',')[-1], m)] += n
    print('=== boundary per (tower, m) ===')
    for k in sorted(per):
        print('  %-6s m=%d : %d' % (k[0], k[1], per[k]))
    tot = sum(n for (t, m, k), n in CEN.items() if k.startswith('BOUNDARY'))
    lev = {j: sum(n for (t, m, k), n in CEN.items()
                  if k.startswith('BOUNDARY') and m == j) for j in (1, 2, 3)}
    sc = sum(n for (t, m, k), n in CEN.items() if k == 'SCORED')
    scope = sum(n for (t, m, k), n in CEN.items() if 'SCOPE-OUT' in k)
    print('TOTALS  roster boundary %d  (m=1 %d, m=2 %d, m=3 %d) | roster '
          'scored %d | evaluator scope-outs %d'
          % (tot, lev[1], lev[2], lev[3], sc, scope))
    j = json.load(open(os.path.join(HERE, 'grt_jb_checks_results.json')))
    rb = sum(v['boundary'] for k, v in j['cread'].items() if '/tw' not in k)
    cb = sum(v['boundary'] for k, v in j['cread'].items() if '/tw' in k)
    print('CROSS-CHECK vs the committed sealed JSON: non-chamber boundary %d '
          '(16-tower roster part %d) + chamber %d = %d ; sealed census field '
          '%d' % (rb, tot, cb, rb + cb, j['censuses']['JB-CREAD-BOUNDARY']))
    print('F1 READOUT: %d of the %d roster boundary rows sit at m = 2 '
          '(inside the stratum the r0 note called unconditional); %d at '
          'm = 3; %d at m = 1; %d evaluator scope-outs.'
          % (lev[2], tot, lev[3], lev[1], scope))


if __name__ == '__main__':
    main()
