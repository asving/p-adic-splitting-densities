"""HE7 r2 SUPPLEMENTARY LEG (post-seal, purely ADDITIVE) — the numeric
verification of LEMMA HE7-12 (SLOT-DOMINATION) and LEMMA HE7-13 (the strict
slope increase), i.e. the machine leg of the r2 repair of PE1 FINDING F-1.

`he7_checks.py` and its artifacts are BYTE-FROZEN at seal 1956151; this file
adds nothing to them: it IMPORTS the sealed runner, regenerates the same
members with the same parameters (the he7r1_supp.py precedent), isolates the
members on which the sealed reader fired the level-2 alpha-refine
(Psi <- Psi - w, w = (LIFT2) at height lam2 with residue s2), and checks the
two r2 lemmas' displayed inequalities member by member.

WHAT F-1 SAYS.  The sealed read applies the S5 package (disk criterion ->
xi-side -> counting -> dictionary) to the REFINED key Psi^(1) = Psi - w,
which is not of DEFINITION HE6-1's form; no displayed lemma of the r1 note
proves the package there.  LEMMA HE7-12 [r2] closes it by SLOT-DOMINATION:
w's Phi'-slots all sit at slot value >= dv2(w) = lam2 > T2 while Psi's
occupied slots sit at exactly T2, so off the level-2 disk

    dv2(w(xi)) - dv2(Psi(xi)) >= (lam2 - T2) + eps1 - l(D'-1) eps0 > 0   (a)

(eps0 = (h - dv xi)^+, eps1 = (u - l*delta)^+, delta = dv(Phi'(xi))), hence
dv2(Psi^(1)(xi)) = dv2(Psi(xi)) off-disk and the whole package transfers.
LEMMA HE7-13 [r2] DERIVES the strict slope increase: at a refine node every
root rho of f has dv2(Psi(rho)) = lam2 with residue matching w's, so
dv2(Psi^(1)(rho)) > lam2 and every slope of the new polygon exceeds lam2.

CHECKS (per refine-firing member of the sealed enumeration):
  B1  slot geometry: every occupied Phi'-slot of Psi has slot value == T2;
      every occupied slot of w has value >= lam2 with min == dv2(w) == lam2
      > T2 (slot-domination), and res2(w, lam2) == s2 ((LIFT2) contract).
  B2  off-disk invariance + the quantitative inequality (a), on FOUR
      off-disk strata (one per offset case of the lemma):
        - g = Phi'                      (delta = infty : eps0 = eps1 = 0)
        - g = Psi_{kappa,-s'} at kappa = (u+2)/2 > lam   (eps0 = eps1 = 0)
        - g = Psi_{kappa,..} at kappa = (2u-1)/4 in (D'h, lam)
                                        (eps0 = 0, eps1 = 1/2 — the exact
                                         middle band of PE1 FINDING F-2)
        - g = x - 1                     (eps0 = 1 > 0, eps1 = u)
        - g = Psi_{lam,-s'} , s' != s   (delta = lam, WRONG residue;
                                         eps0 = eps1 = 0)
      For each: SUM-form of (a) via resultants,
          dv2res(g, w) - dv2res(g, Psi) >= deg(g) * bound(stratum),
      and the invariance conclusion dv2res(g, Psi^(1)) == dv2res(g, Psi),
      where dv2res(g, C) := e1*l*v(Res(g, C)) = sum_{g(xi)=0} dv2(C(xi)).
  B3  LEMMA HE7-13: dv2res(f, Psi) == deg(f)*lam2 (the single side), and
      dv2res(f, Psi^(1)) > deg(f)*lam2 STRICTLY; the recomputed polygon of
      f at Psi^(1) has EVERY slope > lam2; and the label-count identity at
      the REFINED key, dv2res(f, Psi^(1)) == D'' * sum_sides L*lam' (the
      HE7-9(b) identity on Psi^(1) — F-1's gap exercised directly).
  B4  the pre-refine residual is (Z - s2)^2 (read from the sealed trace).
  B5  recount: refine-firing members per row == the FROZEN artifact JSON's
      refines['1'] histogram.  (Recount disclosure: the artifact sums to 42,
      not the 41 of S11's Q1 sentence — checked and reported.)

No PARI needed (identity checks only, both characteristics).  Artifacts:
he7r2_supp_output.txt, he7r2_supp_results.json.
"""
import sys, os, json, time, hashlib
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import he7_checks as H7                                    # noqa: E402
import he6_checks as H6                                    # noqa: E402
from he6_checks import (Zp, FpTring, padd, pmul, development, resultant,
                        key_poly, test_poly, members, disc_nonzero,
                        read_labels, BIG, E1, F1, DP)      # noqa: E402

PINS = ['he7_checks.py', 'he7_checks_results.json', 'he6_checks.py',
        'he7r1_supp.py']

# the sealed runner's thirteen rows, verbatim from he7_checks.main()
ROWS = [
    (Zp, 3, 3, 5, 2, 210, True,  'char 0', 1),
    (Zp, 5, 5, 5, 2, 250, True,  'char 0', 1),
    (Zp, 7, 7, 5, 1, 170, True,  'char 0', 1),
    (Zp, 5, 5, 7, 1, 150, True,  'char 0, deeper side', 1),
    (Zp, 3, 3, 5, 2, 150, True,  'char 0, twist live', 2),
    (Zp, 5, 5, 5, 2, 150, True,  'char 0, twist live', 2),
    (Zp, 5, 5, 5, 1, 120, True,  'char 0, twist live', 3),
    (Zp, 7, 7, 5, 1, 120, True,  'char 0, twist live', 3),
    (Zp, 5, 5, 7, 1, 120, True,  'char 0, deeper+twist', 2),
    (FpTring, 3, 3, 5, 2, 80, False, 'char 3', 1),
    (FpTring, 3, 3, 5, 2, 60, False, 'char 3, twist live', 2),
    (FpTring, 5, 5, 5, 1, 60, False, 'char 5', 1),
    (FpTring, 5, 5, 5, 1, 60, False, 'char 5, twist live', 3),
]

RES = {'rows': [], 'refine_members': 0, 'checks': {}, 'viol': [],
       'pins': {}, 'examples': []}


def md5(path):
    with open(os.path.join(HERE, path), 'rb') as fh:
        return hashlib.md5(fh.read()).hexdigest()


def note(k, n=1):
    RES['checks'][k] = RES['checks'].get(k, 0) + n


def viol(what, detail):
    RES['viol'].append({'what': what, 'detail': str(detail)[:400]})
    print('  !! VIOLATION %s %s' % (what, str(detail)[:220]))


def dv2res(g, C, R, l):
    """sum_{xi: g(xi)=0} dv2(C(xi)) = e1*l*v(Res(g, C)); BIG if Res = 0."""
    r = resultant(g, C)
    if (isinstance(r, int) and r == 0) or (hasattr(r, 'c') and not r.c):
        return BIG
    return E1 * l * R.val(r)


def slot_values(C, fr):
    """occupied Phi'-slot values l*dv(c_s) + s*u of C (any deg <= D'')."""
    cs = development(C, fr.key, fr.l * fr.dr)      # slots s = 0..l*d_r
    out = []
    for s, c in enumerate(cs):
        m = H6.dv_A(c, fr.R)
        if m < BIG:
            out.append((s, fr.l * m + s * fr.u))
    return out


def main():
    t0 = time.time()
    print('HE7 r2 supplementary leg — LEMMA HE7-12 (SLOT-DOMINATION) + '
          'LEMMA HE7-13 (strict slope increase) on the sealed refine-path '
          'members')
    RES['pins'] = {f: md5(f)[:12] for f in PINS if os.path.exists(
        os.path.join(HERE, f))}
    print('pins: ' + ', '.join('%s %s' % kv for kv in RES['pins'].items()))
    frozen = json.load(open(os.path.join(HERE, 'he7_checks_results.json')))
    frozen_ref = {}
    for r in frozen['rows']:
        frozen_ref[(r['ring'], r['s'], r['u'])] = sum(
            v for k, v in r.get('refines', {}).items() if k != '0')
    tot_ref = 0
    for (mk, p, pp, u, W, cap, oracle, tag, s) in ROWS:
        R = mk(p)
        fr = H7.L2Frame(R, pp, u, s)
        lam = Fr(u, 2)
        rco2 = [(s * s) % pp, (-2 * s) % pp]
        row = {'ring': R.name(), 'u': u, 's': s, 'tag': tag, 'members': 0,
               'refine_members': 0, 'B_ok': 0}
        for A, f in members(R, pp, u, rco2, W=W, cap=cap):
            if not disc_nonzero(f, R):
                continue
            rd1 = read_labels(A, R, pp)
            if not rd1['deeper']:
                continue
            row['members'] += 1
            rd2 = H7.level2_read(f, fr)
            if rd2.get('status') != 'OK' or rd2.get('refines', 0) < 1:
                continue
            row['refine_members'] += 1
            tot_ref += 1
            # ---- reconstruct the refine data from the sealed trace
            refs = [e for e in rd2['trace'] if 'refine' in e]
            if len(refs) != rd2['refines']:
                viol('trace/refines mismatch', {'row': tag})
                continue
            lam2 = int(refs[0]['refine'])
            s2 = refs[0]['s2']
            pre = [e for e in rd2['trace'] if 'residual' in e][0]
            w = fr.lift2(lam2, s2)
            Psi1 = padd(fr.Psi, [-c for c in w])
            nf = len(f) - 1
            # ---- B4: the pre-refine residual is (Z - s2)^2
            want = [(s2 * s2) % pp, (-2 * s2) % pp, 1]
            if pre['residual'] != want:
                viol('B4 pre-refine residual != (Z-s2)^2',
                     {'row': tag, 'res': pre['residual'], 's2': s2})
                continue
            note('B4-residual-form')
            # ---- B1: slot geometry (SLOT-DOMINATION)
            sv_Psi = slot_values(fr.Psi, fr)
            sv_w = slot_values(w, fr)
            if any(v != fr.T2 for _, v in sv_Psi):
                viol('B1 Psi has an occupied slot off T2',
                     {'row': tag, 'slots': sv_Psi})
                continue
            if (not sv_w or min(v for _, v in sv_w) != lam2
                    or lam2 <= fr.T2):
                viol('B1 w slot-min != lam2 > T2',
                     {'row': tag, 'slots': sv_w, 'lam2': lam2})
                continue
            if fr.dv2(w) != lam2 or fr.res2(w, lam2) % pp != s2 % pp:
                viol('B1 (LIFT2) contract: dv2(w) or res2(w) wrong',
                     {'row': tag, 'dv2': fr.dv2(w),
                      'res2': fr.res2(w, lam2), 's2': s2})
                continue
            note('B1-slot-domination')
            # ---- B2: off-disk invariance + the quantitative inequality
            #      strata: (g, deg g, eps0, eps1) — all roots share offsets
            sprime = 1 if (s % pp) != 1 else (2 % pp)
            strata = [
                ('Phi\' (delta=infty)', fr.key, 0, Fr(0)),
                ('kappa=(u+2)/2 > lam',
                 test_poly(u + 2, 2, [(-sprime) % pp], R), 0, Fr(0)),
                ('kappa=(2u-1)/4 in (D\'h,lam)',
                 test_poly(2 * u - 1, 4, [(-sprime) % pp], R), 0, Fr(1, 2)),
                ('x - 1 (eps0=1)', [-R.one, R.one], 1, Fr(u)),
                ('delta=lam wrong residue',
                 test_poly(u, 2, [(-sprime) % pp], R), 0, Fr(0)),
            ]
            ok = True
            for name, g, e0, e1 in strata:
                dg = len(g) - 1
                a_psi = dv2res(g, fr.Psi, R, fr.l)
                a_w = dv2res(g, w, R, fr.l)
                a_p1 = dv2res(g, Psi1, R, fr.l)
                bound = (lam2 - fr.T2) + e1 - fr.l * (DP - 1) * e0
                if bound <= 0:
                    viol('B2 bound not positive (lemma case analysis!)',
                         {'row': tag, 'stratum': name, 'bound': str(bound)})
                    ok = False
                    continue
                if a_psi >= BIG or a_p1 >= BIG:
                    viol('B2 resultant vanished on an off-disk stratum',
                         {'row': tag, 'stratum': name})
                    ok = False
                    continue
                if a_w < BIG and Fr(a_w - a_psi) < dg * bound:
                    viol('B2 quantitative inequality FAILS',
                         {'row': tag, 'stratum': name, 'w': a_w,
                          'Psi': a_psi, 'need': str(dg * bound)})
                    ok = False
                    continue
                if a_p1 != a_psi:
                    viol('B2 off-disk invariance FAILS',
                         {'row': tag, 'stratum': name,
                          'Psi': a_psi, 'Psi1': a_p1})
                    ok = False
                    continue
                note('B2-offdisk')
            if not ok:
                continue
            # ---- B3: strict slope increase at the refined key
            a_f0 = dv2res(f, fr.Psi, R, fr.l)
            a_f1 = dv2res(f, Psi1, R, fr.l)
            if a_f0 != nf * lam2:
                viol('B3 pre-refine single side: dv2res(f,Psi) != 8*lam2',
                     {'row': tag, 'got': a_f0, 'want': nf * lam2})
                continue
            if not (a_f1 > nf * lam2):
                viol('B3 dv2res(f,Psi1) not > 8*lam2',
                     {'row': tag, 'got': a_f1})
                continue
            Ad1 = development(f, Psi1, rd2['mu2'])
            dv2s1 = [fr.dv2(Ad1[j]) for j in range(rd2['mu2'])] + [0]
            sides1 = H6.hull_sides(dv2s1)
            slopes1 = [Fr(m1 - m2, j2 - j1) for (j1, m1, j2, m2) in sides1]
            if any(sl <= lam2 for sl in slopes1):
                viol('B3 a post-refine slope <= lam2',
                     {'row': tag, 'slopes': [str(x) for x in slopes1]})
                continue
            tot_Llam = sum(Fr(m1 - m2, j2 - j1) * (j2 - j1)
                           for (j1, m1, j2, m2) in sides1)
            if dv2s1[0] < BIG and Fr(a_f1) != fr.Dpp * tot_Llam:
                viol('B3 HE7-9(b) identity at the REFINED key fails',
                     {'row': tag, 'lhs': a_f1,
                      'rhs': str(fr.Dpp * tot_Llam)})
                continue
            note('B3-strict-slope-increase')
            row['B_ok'] += 1
            if len(RES['examples']) < 4:
                RES['examples'].append(
                    {'ring': R.name(), 's': s, 'u': u, 'T2': fr.T2,
                     'lam2': lam2, 's2': s2,
                     'w_slots': slot_values(w, fr),
                     'Psi_slots': sv_Psi,
                     'dv2res_f_Psi': a_f0, 'dv2res_f_Psi1': a_f1,
                     'post_slopes': [str(x) for x in slopes1]})
        # ---- B5: recount vs the FROZEN artifact
        fro = frozen_ref.get((R.name(), s, u))
        if fro is not None and fro != row['refine_members']:
            viol('B5 refine recount != frozen artifact',
                 {'row': tag, 'frozen': fro, 'got': row['refine_members']})
        else:
            note('B5-recount-row')
        print('  row %-10s u=%d s=%d %-22s members %4d  refine-fired %2d '
              '(frozen %2s)  B-ok %2d'
              % (R.name(), u, s, tag, row['members'], row['refine_members'],
                 fro, row['B_ok']))
        RES['rows'].append(row)
    RES['refine_members'] = tot_ref
    RES['frozen_total'] = sum(frozen_ref.values())
    RES['secs'] = round(time.time() - t0, 1)
    print('\nREFINE-PATH MEMBERS %d (frozen artifact total %d; S11 Q1\'s '
          'sentence says 41 — recount disclosure)'
          % (tot_ref, RES['frozen_total']))
    print('CHECKS %s' % RES['checks'])
    print('VIOLATIONS: %d' % len(RES['viol']))
    print('%.1fs' % (time.time() - t0))
    with open(os.path.join(HERE, 'he7r2_supp_results.json'), 'w') as fh:
        json.dump(RES, fh, indent=1, sort_keys=True, default=str)


if __name__ == '__main__':
    main()
