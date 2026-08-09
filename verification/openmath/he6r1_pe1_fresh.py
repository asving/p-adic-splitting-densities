#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""HE6R1 passPE1 FRESH ROUTE (hostile pass 1 on HE6R1_RECON_2026-08-08.md).

The sealed battery (he6r1_checks.py @ 850e77e) is the only prior machine
route for the ell = 1 / d_r = 2 branch.  This leg opens two NEW routes the
seal never ran; it consumes the sealed instrument by import (md5s printed)
but every predicate scored here is scored against PARI directly.

LEG A (THIRD+ CHARACTERISTIC PAIR).  The seal ran residue characteristics
  {3, 5, 7} in char 0 and {3, 5} in char p.  This leg runs the same
  ell = 1, d_r = 2 frame at p = 11 (r = Z^2 + 1, -1 a non-residue mod 11)
  and p = 13 (r = Z^2 + 2, -2 a non-residue mod 13), full member
  enumeration, reader sigma vs PARI factorpadic member by member.
  PREREGISTERED: 0 mis-decisions; any non-decision must be exactly the
  Psi | f stratum (checked by exact division) and must be decided by the
  LEMMA HE6R1-3 peel with PARI agreement.

LEG B (THE PEEL COMPOSED WITH A REFINE — the interaction the two disclosed
  exception families sit next to; NEVER exercised: the sealed peels all
  landed at mu2 - 1 = 1, where no alpha-refine can occur).  At n = 12
  (mu2 = 3) construct f = Psi * g with g = (Psi - W)^2 + E, W the
  (LIFT2)-lift of a K2-rational residue s2 at an integer level-2 height
  lam2 > T2, and E a deeper perturbation.  Then the read of f must
  (i) hit the Psi | f stratum (peel, LEMMA HE6R1-3), and
  (ii) alpha-refine the peeled g at the double root (Z - s2)^2 (THEOREM
       HE7.A(3), ell2 * d_r2 = 1 branch),
  before deciding.  sigma(f) = {(2,2)} (the peeled Psi) + read(g), scored
  against PARI.  Frames at p in {3, 5}; E ranges over height-(2*lam2+1)
  and height-(2*lam2+2) perturbations (both parities of the post-refine
  slope), disc f != 0 enforced, PARI on every member.

NOT run here: non-prime q (an f1 >= 2 / K = F_{q^2} tower needs a fresh
K2-over-K implementation; disclosed as the remaining fresh-route candidate).

Artifacts: he6r1_pe1_fresh_output.txt, he6r1_pe1_fresh_results.json.
"""

import sys, os, json, time, hashlib
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import he6r1_checks as M
from he6r1_checks import L2Frame1, level2_read, members1
import he6_checks as H6
from he6_checks import (Zp, padd, pmul, ppow, development, resultant,
                        disc_nonzero, gp_sig_batch, polystr, BIG, E1, F1)
import he6r1_supp as SUPP   # peel_read (LEMMA HE6R1-3 applied first)

RES = {'legA': {}, 'legB': {}, 'viol': [], 'pins': {}}
for f in ['he6r1_checks.py', 'he6_checks.py', 'he6r1_supp.py']:
    RES['pins'][f] = hashlib.md5(open(os.path.join(HERE, f), 'rb').read()).hexdigest()
print('import pins:', json.dumps(RES['pins']))


def viol(leg, what, detail):
    RES['viol'].append({'leg': leg, 'what': what, 'detail': str(detail)[:300]})
    print('  !! VIOLATION %s %s %s' % (leg, what, str(detail)[:200]))


def pdivides(Psi, f):
    """exact monic division test in Z[x] (own integer code, not the reader's)."""
    f = [int(c) for c in f]
    dP = len(Psi) - 1
    while len(f) - 1 >= dP:
        lead = f[-1]
        if lead == 0:
            f.pop(); continue
        off = len(f) - 1 - dP
        for i, c in enumerate(Psi):
            f[off + i] = f[off + i] - lead * int(c)
        f.pop()
    return all(c == 0 for c in f)


# ============================================ LEG A: p = 11 and p = 13
def legA():
    out = {}
    for (p, c0, c1) in [(11, 1, 0), (13, 2, 0)]:
        R = Zp(p)
        u = 3
        fr = L2Frame1(R, p, u, c0, c1)
        t0 = time.time()
        recs, jobs = [], []
        nmem = ndec = 0
        for A, f in members1(R, p, u, c0, c1, W=2, cap=140):
            if not disc_nonzero(f, R):
                continue
            nmem += 1
            rd = level2_read(f, fr)
            if rd['status'] != 'OK':
                # must be exactly the Psi | f stratum, and the peel must decide
                if not pdivides(fr.Psi, f):
                    viol('A-STRATUM', 'non-decision OFF the Psi|f stratum',
                         dict(p=p, status=rd['status'], f=polystr(f)))
                    continue
                pr = SUPP.peel_read(f, fr)
                if pr['status'] != 'OK':
                    viol('A-PEEL', 'peel did not decide',
                         dict(p=p, status=pr['status'], f=polystr(f)))
                    continue
                recs.append((polystr(f), tuple(sorted(pr['sigma'])),
                             'PEEL%d' % pr['peels']))
                jobs.append(polystr(f))
                continue
            ndec += 1
            recs.append((polystr(f), rd['sigma'], 'OK'))
            jobs.append(polystr(f))
        got = gp_sig_batch([(j, None) for j in jobs], p)
        agree = mism = 0
        sigcounts = {}
        for i, (fs, sg, st) in enumerate(recs):
            pari = got.get(i)
            if pari is None:
                viol('A-PARI', 'no PARI result', dict(p=p, i=i)); continue
            if tuple(sorted(pari)) == tuple(sorted(sg)):
                agree += 1
            else:
                mism += 1
                viol('A-SIG', 'read != PARI',
                     dict(p=p, read=sg, pari=pari, f=fs, st=st))
            k = str(tuple(sorted(sg)))
            sigcounts[k] = sigcounts.get(k, 0) + 1
        out[str(p)] = dict(members=nmem, decided=ndec, pari_jobs=len(jobs),
                           agree=agree, mismatch=mism, sig=sigcounts,
                           secs=round(time.time() - t0, 1))
        print('LEG A p=%d: members %d decided %d pari %d agree %d mismatch %d'
              % (p, nmem, ndec, len(jobs), agree, mism))
        print('        sigma census:', json.dumps(sigcounts))
    RES['legA'] = out


# ================================= LEG B: peel COMPOSED WITH a refine, n=12
def legB():
    out = {}
    for (p, c0, c1) in [(3, 1, 0), (5, 2, 0)]:
        R = Zp(p)
        u = 3
        fr = L2Frame1(R, p, u, c0, c1)
        lam2 = 2 * u + 1                       # integer level-2 height > T2
        t0 = time.time()
        recs, jobs = [], []
        npeel = nref = 0
        for s0 in range(p):
            for s1 in range(p):
                if s0 == 0 and s1 == 0:
                    continue
                s2 = (s0, s1)                  # K2-rational residue, != 0
                W = fr.lift2(lam2, s2)
                if W is None:
                    continue
                gm = padd(fr.Psi, [x * R.el(-1) for x in W])  # Psi - W
                g0 = pmul(gm, gm)                             # (Psi - W)^2
                for dE in (2 * lam2 + 1, 2 * lam2 + 2):
                    for cE in (1, 2):
                        # E = cE * nrm(dE): a single deep monomial block
                        E = [x * R.el(cE) for x in H6.nrm(dE, R)]
                        g = padd(g0, E)
                        f = pmul(fr.Psi, g)
                        if not disc_nonzero(f, R):
                            continue
                        pr = SUPP.peel_read(f, fr)
                        if pr['status'] != 'OK':
                            viol('B-PEEL', 'peel+read did not decide',
                                 dict(p=p, s2=s2, dE=dE, cE=cE,
                                      status=pr['status']))
                            continue
                        sg, peels = pr['sigma'], pr['peels']
                        # count refines on the peeled part
                        rdg = level2_read(g, fr)
                        refs = rdg.get('refines') if rdg['status'] == 'OK' else None
                        if refs:
                            nref += 1
                        npeel += peels
                        recs.append((polystr(f), tuple(sorted(sg)),
                                     peels, refs))
                        jobs.append(polystr(f))
        got = gp_sig_batch([(j, None) for j in jobs], p)
        agree = mism = 0
        sigcounts = {}
        for i, (fs, sg, peels, refs) in enumerate(recs):
            pari = got.get(i)
            if pari is None:
                viol('B-PARI', 'no PARI result', dict(p=p, i=i)); continue
            if tuple(sorted(pari)) == tuple(sorted(sg)):
                agree += 1
            else:
                mism += 1
                viol('B-SIG', 'peel-refine read != PARI',
                     dict(p=p, read=sg, pari=pari, peels=peels, refs=refs,
                          f=fs))
            k = str(tuple(sorted(sg)))
            sigcounts[k] = sigcounts.get(k, 0) + 1
        out[str(p)] = dict(members=len(recs), peels=npeel,
                           members_with_refine=nref, agree=agree,
                           mismatch=mism, sig=sigcounts,
                           secs=round(time.time() - t0, 1))
        print('LEG B p=%d: members %d (peels %d, with-refine %d) agree %d '
              'mismatch %d' % (p, len(recs), npeel, nref, agree, mism))
        print('        sigma census:', json.dumps(sigcounts))
    RES['legB'] = out


def main():
    t0 = time.time()
    legA()
    legB()
    print('\n===================== SUMMARY =====================')
    print('legA:', json.dumps(RES['legA']))
    print('legB:', json.dumps(RES['legB']))
    print('violations:', len(RES['viol']))
    print('seconds  :', round(time.time() - t0, 1))
    with open(os.path.join(HERE, 'he6r1_pe1_fresh_results.json'), 'w') as fh:
        json.dump(RES, fh, indent=1, default=str)
    return 1 if RES['viol'] else 0


if __name__ == '__main__':
    sys.exit(main())
