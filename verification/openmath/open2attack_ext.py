#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
open2attack_ext.py -- POST-SEAL EXTENSION leg of open2attack_checks.py
(W2-OPEN-2 ATTACK unit).  Honest status: EXPLORATORY-EXT.  The sealed
battery (commit-1 runner, byte-intact) predicted >= 1 spurious-selection
row at m >= 2 (OA-SPUR) and observed 0: every byte-equal m >= 2 junction
it generated had spurious-free selection geography (all its stabilizer-rich
sparse-support moduli landed on byte-RED junctions).  This extension was
designed AFTER seeing that table (hence EXPLORATORY-EXT), targeting the
geography derivably: on a (C-coll) chamber byte-equality at the top
junction is guaranteed by the trivial character, so a stabilizer-rich
binomial modulus there must produce the spurious recording.

PREDICTIONS (written before this leg was first run; derivations in the
note Sec 5):
  EXT-A  F9 (C-coll) chamber Z3 (1,1,1)+(3,1,2), top read (1,1)/(2,1) x
         psi2 = y^4+c (irreducible ones; d = 4): byte-equal m=2 junctions
         with recorded xi = z2 != 1 (z2 is 4-torsion and precedes 1 in
         F9 enumeration order) -- SPURIOUS at m=2; strict; the forward
         families stay green.
  EXT-B  F64 (C-coll) chamber Z2 (1,1,2)+(1,1,3) (psi0 = y^2+y+1,
         psi1 = y^3+zeta), top read (1,1)/(2,1) x psi2 = y^3+c
         (c non-cube; d = 3): byte-equal m=2 junctions with recorded
         xi = zeta != 1 (zeta precedes 1 in F64 enumeration) -- SPURIOUS
         at m=2; strict; forward families green.
  EXT-C  the literal PE3 counter-instance chamber Z2 (1,1,2)+(2,1,3)
         extended by a third read (PE4 o-e's "append any third read",
         instantiated and MEASURED): the chamber's own r=3 stays the PE3
         spurious row; the m=2 junctions above it are walked (bytes below
         ARE shared -- PE3's junction is byte-equal) and the forward
         families stay green there.
All sealed check families run unchanged on these rows (imported from the
sealed runner); results go to open2attack_ext_output.txt / _results.json.
"""
import sys, os, json, time, collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawn_pe_reimpl as ITL
import grt_weld_probe as GWP
import open2attack_checks as OA

def ext_specs():
    out = []
    # EXT-A: F9 (C-coll) quartic binomials
    ch = dict(id='EXTACH', ring='Zp', p=3, d0=1, Phi0=[0, 1],
              reads=[(1, 1, 1), (3, 1, 2)], psi=[[1, 1], [1, 0, 1]])
    T = OA.build_tower_x(ch)
    K2 = T.K[2]
    for (e2, h2) in [(1, 1), (2, 1)]:
        cands = OA.enum_psi_cands(K2, {4}, 'sample')
        for i, cand in enumerate(cands):
            out.append((dict(id='EXTA-%d%d-%02d' % (e2, h2, i), ring='Zp',
                             p=3, d0=1, Phi0=[0, 1],
                             reads=[(1, 1, 1), (3, 1, 2), (e2, h2, 4)],
                             psi=[[1, 1], [1, 0, 1], cand]), 'EXTA'))
    # EXT-B: F64 (C-coll) cubic binomials
    chb = dict(id='EXTBCH', ring='Zp', p=2, d0=1, Phi0=[0, 1],
               reads=[(1, 1, 2), (1, 1, 3)],
               psi=[[1, 1, 1], [('z', 1, 1), 0, 0, 1]])
    Tb = OA.build_tower_x(chb)
    K64 = Tb.K[2]
    z2 = Tb.z[2]
    picks = []
    x = K64.one()
    for k in range(8):
        x = K64.mul(x, z2)
        picks.append(x)
    for (e2, h2) in [(1, 1), (2, 1)]:
        n = 0
        for i, c in enumerate(picks):
            cand = [c, K64.zero(), K64.zero(), K64.one()]
            if not OA.poly_irr(K64, cand):
                continue
            n += 1
            out.append((dict(id='EXTB-%d%d-%02d' % (e2, h2, i), ring='Zp',
                             p=2, d0=1, Phi0=[0, 1],
                             reads=[(1, 1, 2), (1, 1, 3), (e2, h2, 3)],
                             psi=[[1, 1, 1], [('z', 1, 1), 0, 0, 1],
                                  [('RAW', cc) for cc in cand]]), 'EXTB'))
            if n >= 4:
                break
    # EXT-C: the literal PE3 chamber + third reads
    chc = dict(id='EXTCCH', ring='Zp', p=2, d0=1, Phi0=[0, 1],
               reads=[(1, 1, 2), (2, 1, 3)],
               psi=[[1, 1, 1], [('z', 1, 1), 0, 0, 1]])
    Tc = OA.build_tower_x(chc)
    Kc = Tc.K[2]
    zc = Tc.z[2]
    picksc = [Kc.one(), zc, Kc.mul(zc, zc),
              Tc.embed(Tc.z[1], 1, 2)]
    for (e2, h2) in [(1, 1), (2, 1)]:
        for i, c in enumerate(picksc):
            out.append((dict(id='EXTC-%d%d-%02d' % (e2, h2, i), ring='Zp',
                             p=2, d0=1, Phi0=[0, 1],
                             reads=[(1, 1, 2), (2, 1, 3), (e2, h2, 1)],
                             psi=[[1, 1, 1], [('z', 1, 1), 0, 0, 1],
                                  [('RAW', c), ('RAW', Kc.one())]]), 'EXTC'))
    return out

def main():
    t0 = time.time()
    lines = []

    def emit(s=''):
        print(s)
        lines.append(s)

    emit('open2attack_ext -- POST-SEAL EXTENSION (EXPLORATORY-EXT): the '
         'm >= 2 spurious-selection geography, targeted')
    specs = ext_specs()
    emit('extension battery: %d tower specs' % len(specs))
    built = 0
    for spec, genre in specs:
        tag = '%s,p=%d,%s' % (spec['ring'], spec['p'], spec['id'])
        try:
            T = OA.build_tower_x(spec)
            G = GWP.gmn_from_tower(T)
        except AssertionError:
            continue
        built += 1
        OA.analyze_tower(T, G, tag, genre)
    emit('  built %d towers, %d junction rows' % (built, len(OA.ROWS)))
    cens = collections.defaultdict(int)
    spur_rows = []
    for row in OA.ROWS:
        if row.get('status') == 'SKIP' or 'strict' not in row:
            cens['skip_or_degen'] += 1
            continue
        k = 'M%d' % row['M']
        cens['walked_' + k] += 1
        if row.get('spurious'):
            cens['spurious_' + k] += 1
            if row['M'] >= 2:
                spur_rows.append((row['tag'], row['r'], row['orbit'],
                                  row['byte_equal'], row['strict']))
        if row['strict'] and not row['byte_equal']:
            cens['STRICT_BYTE_RED_' + k] += 1
    emit('censuses: %s' % json.dumps(dict(sorted(cens.items()))))
    emit()
    for fam, desc, pred in OA.FAMS:
        obs = sum(1 for v in OA.VIOL if v[0] == fam)
        nsm = OA.COUNTS.get(fam, 0)
        if nsm == 0:
            continue
        emit('%-11s %-48s pred %-2s obs %4d (%5d)  %s'
             % (fam, desc, pred, obs, nsm,
                'GREEN' if obs == 0 else
                ('FINDING' if pred == '?' else 'RED')))
    emit()
    nspur2 = cens.get('spurious_M2', 0) + cens.get('spurious_M3', 0)
    emit('EXT VERDICT: spurious rows at m >= 2: %d (PREDICT >= 1 on '
         'EXT-A/EXT-B)' % nspur2)
    for s in spur_rows[:10]:
        emit('   SPUR-M2+: %s' % (s,))
    if OA.VIOL:
        emit('%d violations/findings:' % len(OA.VIOL))
        for v in OA.VIOL[:40]:
            emit('   %s' % (v,))
    here = os.path.dirname(os.path.abspath(__file__))
    RES = {'rows': OA.ROWS,
           'violations': [list(v) for v in OA.VIOL],
           'censuses': dict(cens),
           'spur_m2_rows': spur_rows,
           'elapsed_s': round(time.time()-t0, 1)}
    with open(os.path.join(here, 'open2attack_ext_results.json'), 'w') as fh:
        json.dump(RES, fh, indent=1, default=repr)
    with open(os.path.join(here, 'open2attack_ext_output.txt'), 'w') as fh:
        fh.write('\n'.join(lines) + '\n')
    hard = any(v[0] for v in OA.VIOL
               if v[0] not in ('OA-FWD-M2', 'OA-FWD-M3', 'OA-FWD-REC'))
    return 0 if (not hard and nspur2 >= 1) else 1

if __name__ == '__main__':
    sys.exit(main())
