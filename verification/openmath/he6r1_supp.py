#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""HE6 r1 — POST-SEAL SUPPLEMENTARY DIAGNOSTIC (explicitly OUTSIDE the sealed
battery `he6r1_checks.py`; the sealed runner, its output and its json are
untouched).  Two items, both raised BY the sealed run's own violation list:

(A) THE Psi | f_S STRATUM (12 of 932 members; the level-2 analogue of Codex
    HE6-PE1 finding 2's Phi' | f stratum).  The sealed reader has no guard
    for A_0^{(2)} = 0 (i.e. the level-2 key divides f), so it reports
    BADTOTAL: the level-2 polygon loses the j = 0 pin, one block goes
    missing, and the block sizes do not sum to deg f.  LEMMA HE6R1-3 (the
    level-2 peel) says: if Psi | f_S then gcd(f_S, Psi) = Psi is a single
    monic IRREDUCIBLE factor of degree D'' with (e, f) = (e1*ell, f1*d_r),
    and the read continues on f_S/Psi with mu2 - 1.  This leg applies that
    peel to every violating member and scores the result against PARI.

(B) THE POST-REFINE P5 INSTANCES (4 of 50).  The sealed P5 grid takes the
    level-2 labels from the reader's FINAL state — after a level-2
    alpha-refine Psi -> Psi' = Psi - w — but builds the test polynomial
    Psi2 over the ORIGINAL Psi, so at those instances the strict-excess
    identity is being tested at a label that belongs to a different key.
    This leg rebuilds Psi2 over the REFINED key and re-tests strict excess.

Both items are DISCLOSED as post-seal; neither edits a sealed predicate.
Artifact: he6r1_supp_output.txt.
"""

import sys, os, json
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import he6r1_checks as M
from he6_checks import (Zp, FpTring, padd, pmul, ppow, development, resultant,
                        disc_nonzero, polystr, gp_sig_batch, BIG, E1, F1, DP)

ROWS = [(Zp(3), 3, 3, 1, 0), (Zp(5), 5, 3, 2, 0), (Zp(5), 5, 3, 1, 1),
        (Zp(7), 7, 3, 3, 1), (Zp(5), 5, 5, 2, 0),
        (FpTring(3), 3, 3, 1, 0), (FpTring(5), 5, 3, 2, 0)]

OUT = {'peel': [], 'refine': [], 'summary': {}}


def peel_read(f, fr):
    """LEMMA HE6R1-3 + the level-2 read: peel every Psi-factor first."""
    blocks, cur, peels = [], f, 0
    while True:
        mu2 = (len(cur) - 1) // fr.Dpp
        if mu2 < 1:
            break
        Ad = development(cur, fr.Psi, mu2)
        if any(c for c in Ad[0]):
            break                      # Psi does not divide cur
        # cur = Psi * q  with  q = sum_{j>=1} A_j Psi^{j-1}
        q = [fr.R.zero]
        powk = [fr.R.one]
        for j in range(1, mu2):
            q = padd(q, pmul(Ad[j], powk))
            powk = pmul(powk, fr.Psi)
        q = padd(q, powk)
        assert len(q) - 1 == len(cur) - 1 - fr.Dpp, 'peel degree bookkeeping'
        blocks.append((E1 * fr.l, F1 * fr.dr))     # (e1*ell, f1*d_r)
        cur, peels = q, peels + 1
    rd = M.level2_read(cur, fr) if len(cur) - 1 >= fr.Dpp else \
        {'status': 'TRIVIAL', 'sigma': ()}
    if rd['status'] != 'OK':
        return {'status': 'PEEL-' + rd['status'], 'peels': peels}
    return {'status': 'OK', 'peels': peels,
            'sigma': tuple(sorted(blocks + list(rd['sigma'])))}


def item_A():
    print('== (A) the Psi | f_S stratum: LEMMA HE6R1-3 peel vs PARI ==')
    tot, ok, jobs, recs = 0, 0, [], []
    for (R, p, u, c0, c1) in ROWS:
        fr = M.L2Frame1(R, p, u, c0, c1)
        for A, f in M.members1(R, p, u, c0, c1, W=2, cap=140):
            if not disc_nonzero(f, R):
                continue
            rd = M.level2_read(f, fr)
            if rd['status'] == 'OK':
                continue
            tot += 1
            pr = peel_read(f, fr)
            rec = dict(ring=R.name(), p=p, lam=u, r=(c0, c1),
                       sealed_status=rd['status'], peel=pr.get('status'),
                       peels=pr.get('peels'), sigma=str(pr.get('sigma')))
            recs.append(rec)
            if pr['status'] == 'OK':
                ok += 1
            if R.char0:
                jobs.append((polystr(f), len(recs) - 1))
    got = {}
    if jobs:
        res = gp_sig_batch([(j[0], None) for j in jobs], ROWS[0][1])
        # group by prime: gp_sig_batch takes ONE p, so re-run per prime
        got = {}
    agree, checked = 0, 0
    byp = {}
    for ps, idx in jobs:
        byp.setdefault(recs[idx]['p'], []).append((ps, idx))
    for p, js in byp.items():
        res = gp_sig_batch([(ps, None) for ps, _ in js], p)
        for i, (ps, idx) in enumerate(js):
            if i not in res:
                continue
            sg = tuple(sorted(tuple(x) for x in res[i]))
            recs[idx]['pari'] = str(sg)
            checked += 1
            if str(sg) == recs[idx]['sigma']:
                agree += 1
                recs[idx]['verdict'] = 'AGREE'
            else:
                recs[idx]['verdict'] = 'MISMATCH'
    OUT['peel'] = recs
    OUT['summary']['peel'] = dict(degenerate_members=tot, peel_decided=ok,
                                  pari_checked=checked, pari_agree=agree)
    print('   degenerate members %d  peel-decided %d  PARI-checked %d  agree %d'
          % (tot, ok, checked, agree))
    for r in recs:
        print('   ', r.get('ring'), 'lam', r.get('lam'), r.get('sealed_status'),
              '-> peels', r.get('peels'), r.get('sigma'),
              r.get('pari', '(char p: no oracle)'), r.get('verdict', ''))


def item_B():
    print('\n== (B) the post-refine P5 instances: rebuild Psi2 over the '
          'REFINED key ==')
    n_re, n_ok = 0, 0
    for (R, p, u, c0, c1) in ROWS:
        if not R.char0:
            continue
        fr = M.L2Frame1(R, p, u, c0, c1)
        cnt = 0
        for A, f in M.members1(R, p, u, c0, c1, W=2, cap=140):
            if not disc_nonzero(f, R):
                continue
            cnt += 1
            if cnt > 6:
                break
            rd = M.level2_read(f, fr)
            if rd['status'] != 'OK' or not rd.get('refines'):
                continue
            # replay the refine chain to recover the FINAL key
            Psi = fr.Psi
            mu2 = (len(f) - 1) // fr.Dpp
            for step in rd['trace']:
                if 'refine' not in step:
                    continue
                lam2 = Fr(step['refine'])
                s2 = tuple(step['s2'])
                w = fr.lift2(int(lam2), s2)
                Psi = padd(Psi, [-c for c in w])
            saved = fr.Psi
            fr.Psi = Psi                    # local, in-memory only
            Ad = development(f, Psi, mu2)
            dv2s = [fr.dv2(Ad[j]) for j in range(mu2 + 1)]
            for (u2, l2, r2, exp) in M.grid2_labels(f, fr):
                P2 = M.build_psi2(fr, u2, l2, r2)
                if P2 is None:
                    continue
                rr = resultant(f, P2)
                if rr == 0 or (hasattr(rr, 'c') and not rr):
                    got = BIG
                else:
                    got = E1 * fr.l * R.val(rr)
                flat = fr.Dpp * l2 * len(r2) * M.h_F2(dv2s, Fr(u2, l2))
                n_re += 1
                good = got > flat
                n_ok += 1 if good else 0
                OUT['refine'].append(dict(p=p, lam=u, lam2='%d/%d' % (u2, l2),
                                          got=got, flat=str(flat),
                                          strict=bool(good)))
                print('   p=%d lam=%d refined-key label %d/%d: got %s flat %s %s'
                      % (p, u, u2, l2, got, flat, 'STRICT' if good else 'FLAT'))
            fr.Psi = saved
    OUT['summary']['refine'] = dict(instances=n_re, strict=n_ok)
    print('   post-refine label instances %d, strict excess %d' % (n_re, n_ok))


if __name__ == '__main__':
    item_A()
    item_B()
    with open(os.path.join(HERE, 'he6r1_supp_results.json'), 'w') as fh:
        json.dump(OUT, fh, indent=1, default=str)
    print('\nSUMMARY', json.dumps(OUT['summary']))
