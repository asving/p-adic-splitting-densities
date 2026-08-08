"""HE7 r1 SUPPLEMENTARY LEG (post-seal, purely ADDITIVE).

`he7_checks.py` and its artifacts (`he7_checks_output.txt`,
`he7_checks_results.json`) are BYTE-FROZEN at seal 1956151.  This file adds
nothing to them: it IMPORTS the sealed runner, regenerates the same members
with the same parameters, and runs one new check on a stratum the sealed
runner isolated but declined to decide.

WHAT IT CHECKS — FINDING HE6R1-F2 / LEMMA HE6R1-3 (the level-2 peel), in
HE7's OWN frame.  The sealed run reported

    status DEGENERATE-key-divides : 8 members of 1,587

i.e. members whose level-2 Psi-development has A_0^(2) = 0, equivalently
Psi | f_S: the level-2 polygon loses its j = 0 pin and the reader returns no
sigma (2 of the 8 sit on a PARI row, which is why that row shows
members 124 / PARI 122).  HE6R1-F2 names the missing hypothesis
(THEOREM HE7.A and COROLLARY HE7-7'' need Psi ) f_S) and LEMMA HE6R1-3 is
the cure:

    Psi | f_S  =>  gcd(f_S, Psi) = Psi, Psi is IRREDUCIBLE over O of degree
    D'' with (e, f) = (e_1 l, f_1 d_r), it is a SIMPLE factor, and
    f_S = Psi * f_S' with Psi ) f_S' and mu_2 - 1 in place of mu_2.

At HE7's frame (e_1, f_1, h) = (2, 1, 1), l = 2, d_r = 1, D'' = 4, mu_2 = 2
the lemma therefore predicts, member by member on that stratum,

    sigma(f) = {(e_1 l, f_1 d_r)} u sigma(f_S')
             = {(4, 1)} u {(4, 1)} = {(4,1), (4,1)},

with f_S' = Psi + A_1^(2) of degree D'' = 4 and mu_2' = 1.  Note this letter
is INSIDE the three-sigma alphabet of §S8, so the n = 8 dictionary's
"no fourth value possible" survives the added row.

CHECKS (per degenerate member):
  A1  A_0^(2) = 0 and Psi * (Psi + A_1^(2)) = f  EXACTLY in O[x]      (peel)
  A2  A_1^(2) != 0, so Psi ) f_S' -- the peel happens AT MOST ONCE
  A3  the sealed reader, re-run on f_S', returns status OK with
      sigma(f_S') = ((4,1),)  (mu_2' = 1)
  A4  [char 0 only] PARI factorpadic: sigma(f) == ((4,1),(4,1))
  A5  [char 0 only] PARI factorpadic: sigma(Psi) == ((4,1),) -- a DIRECT
      test of LEMMA HE6R1-3's irreducibility + (e, f) = (e_1 l, f_1 d_r)

A4/A5 are the non-textual leg: they do not consult the peel's proof, only
PARI.  Artifacts: he7r1_supp_output.txt, he7r1_supp_results.json.
"""
import sys, os, json, time, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import he7_checks as H7                                    # noqa: E402
import he6_checks as H6                                    # noqa: E402
from he6_checks import (Zp, FpTring, padd, pmul, development, polystr,
                        gp_sig_batch, members, disc_nonzero, read_labels,
                        BIG, E1, F1, DP)                    # noqa: E402

PINS = ['he7_checks.py', 'he7_checks_results.json', 'he6_checks.py']

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

RES = {'rows': [], 'members_seen': 0, 'degenerate': 0, 'checks': {},
       'viol': [], 'pins': {}}


def md5(path):
    with open(os.path.join(HERE, path), 'rb') as fh:
        return hashlib.md5(fh.read()).hexdigest()


def note(k, n=1):
    RES['checks'][k] = RES['checks'].get(k, 0) + n


def viol(what, detail):
    RES['viol'].append({'what': what, 'detail': str(detail)[:400]})
    print('  !! VIOLATION %s %s' % (what, str(detail)[:200]))


def pzero(f):
    return all(not c for c in f)


def peq(a, b):
    n = max(len(a), len(b))
    for i in range(n):
        ca = a[i] if i < len(a) else 0
        cb = b[i] if i < len(b) else 0
        if ca != cb:
            return False
    return True


def main():
    t0 = time.time()
    print('HE7 r1 supplementary leg — the level-2 PEEL (LEMMA HE6R1-3) on '
          "HE7's own Psi | f_S stratum")
    RES['pins'] = {f: md5(f)[:12] for f in PINS if os.path.exists(
        os.path.join(HERE, f))}
    print('pins: ' + ', '.join('%s %s' % kv for kv in RES['pins'].items()))
    tot_deg = 0
    pari_jobs, pari_tags = [], []
    for (mk, p, pp, u, W, cap, oracle, tag, s) in ROWS:
        R = mk(p)
        fr = H7.L2Frame(R, pp, u, s)
        rco2 = [(s * s) % pp, (-2 * s) % pp]
        row = {'ring': R.name(), 'u': u, 's': s, 'tag': tag, 'members': 0,
               'degenerate': 0, 'peel_ok': 0, 'sigma_pred': {}}
        for A, f in members(R, pp, u, rco2, W=W, cap=cap):
            if not disc_nonzero(f, R):
                continue
            rd1 = read_labels(A, R, pp)
            if not rd1['deeper']:
                continue
            row['members'] += 1
            rd2 = H7.level2_read(f, fr)
            if rd2['status'] != 'DEGENERATE-key-divides':
                continue
            row['degenerate'] += 1
            tot_deg += 1
            # ---- A1: A_0^(2) = 0 and the peel is exact
            Ad = development(f, fr.Psi, 2)
            if not pzero(Ad[0]):
                viol('A1 A_0^(2) != 0 on the key-divides stratum',
                     {'row': tag, 'ring': R.name()})
                continue
            fsp = padd(fr.Psi, Ad[1])
            if not peq(pmul(fr.Psi, fsp), f):
                viol('A1 peel not exact: Psi*(Psi+A_1) != f',
                     {'row': tag, 'ring': R.name()})
                continue
            note('A1-peel-exact')
            # ---- A2: A_1^(2) != 0, so Psi does not divide f_S' (one peel)
            if pzero(Ad[1]):
                viol('A2 A_1^(2) = 0: f = Psi^2, disc f = 0 should have '
                     'filtered it', {'row': tag})
                continue
            note('A2-single-peel')
            # ---- A3: the sealed reader decides f_S' at mu_2' = 1
            rd = H7.level2_read(fsp, fr)
            if rd.get('status') != 'OK':
                viol('A3 reader failed on the peeled factor',
                     {'row': tag, 'status': rd.get('status')})
                continue
            sg_peeled = tuple(sorted(tuple(x) for x in rd['sigma']))
            if sg_peeled != ((E1 * fr.l, F1 * fr.dr),):
                viol('A3 peeled sigma != ((e_1 l, f_1 d_r),)',
                     {'row': tag, 'got': str(sg_peeled)})
                continue
            note('A3-peeled-read')
            pred = tuple(sorted([(E1 * fr.l, F1 * fr.dr)] + list(sg_peeled)))
            row['sigma_pred'][str(pred)] = row['sigma_pred'].get(
                str(pred), 0) + 1
            row['peel_ok'] += 1
            if oracle:
                pari_jobs.append((polystr(f), None))
                pari_tags.append((tag, R.name(), pred, 'f'))
                pari_jobs.append((polystr(fr.Psi), None))
                pari_tags.append((tag, R.name(),
                                  ((E1 * fr.l, F1 * fr.dr),), 'Psi'))
        print('  row %-10s u=%d s=%d %-22s members %4d  key-divides %d  '
              'peel-decided %d  %s'
              % (R.name(), u, s, tag, row['members'], row['degenerate'],
                 row['peel_ok'], row['sigma_pred']))
        RES['rows'].append(row)
        RES['members_seen'] += row['members']
    RES['degenerate'] = tot_deg
    # ---- A4/A5: PARI, batched per prime
    print('\n--- PARI leg (A4: sigma(f); A5: sigma(Psi) = the peel letter)')
    by_p = {}
    for job, tg in zip(pari_jobs, pari_tags):
        pp = int(tg[1].split('_')[1]) if tg[1].startswith('Z_') else None
        by_p.setdefault(pp, []).append((job, tg))
    agree = {'f': [0, 0], 'Psi': [0, 0]}
    for pp, items in sorted(by_p.items()):
        got = gp_sig_batch([j for j, _ in items], pp)
        for i, (job, tg) in enumerate(items):
            g = got.get(i)
            kind = tg[3]
            if g is None:
                viol('A4/A5 PARI returned nothing', {'tag': tg})
                continue
            agree[kind][1] += 1
            gg = tuple(sorted(tuple(x) for x in g))
            if gg == tg[2]:
                agree[kind][0] += 1
                note('A4-pari-sigma-f' if kind == 'f' else 'A5-pari-sigma-Psi')
            else:
                viol('A4/A5 PARI disagrees with the peel prediction',
                     {'tag': str(tg), 'pari': str(gg)})
    print('  A4 sigma(f)   predicted {(4,1),(4,1)} : %d/%d PARI agree'
          % tuple(agree['f']))
    print('  A5 sigma(Psi) predicted {(4,1)}       : %d/%d PARI agree'
          % tuple(agree['Psi']))
    RES['pari'] = {'sigma_f': agree['f'], 'sigma_Psi': agree['Psi']}
    RES['secs'] = round(time.time() - t0, 1)
    print('\nMEMBERS %d  KEY-DIVIDES %d  CHECKS %s'
          % (RES['members_seen'], RES['degenerate'], RES['checks']))
    print('VIOLATIONS: %d' % len(RES['viol']))
    print('%.1fs' % (time.time() - t0))
    with open(os.path.join(HERE, 'he7r1_supp_results.json'), 'w') as fh:
        json.dump(RES, fh, indent=1, sort_keys=True, default=str)


if __name__ == '__main__':
    main()
