#!/usr/bin/env python3
"""GENTOW2 passPE1 FRESH ROUTE (hostile verifier, 2026-08-09).

Boundary-configuration witnesses the sealed battery does NOT cover:
no committed witness has BOTH K2 = F4 (nontrivial level-2 residue
units, where Def-3.15 epsilon/cocycle effects can live) AND f3 >= 2
(multiple K2-digits at different Gamma_2 grades) — N1 is F4 with
f3 = 1, N2 is f3 = 2 with K2 = F2. This is exactly the corner where
the note's B-2 identification (repo digit = eps-normalized FGMN
Def-3.16 coordinate) is load-bearing and machine-unwitnessed.

All at the N1 tower (Phi' = x^2-2, Phi2b = Phi'^2 - 2x*Phi' - 8;
profile e1=2, f1=1, e2=1, f2=2, u2=3, psi2 = T^2+T+1, K2 = F4 =
F2(eta2), eta2 = class(Phi'(xi)/2x(xi))). Ladder heights
dv2(pi^a x^i Phi'^b) = 2a + i + 3b. Digit table used (derived before
running): height 7: n(7) = 8x (class 1), 4*Phi' has class eta2;
height 13: n(13) = 64x (class 1), 32*Phi' class eta2; height 14:
n(14) = 128 (class 1), 32*x*Phi' class eta2 (x^2/2 = 1 + Phi'/2 has
class 1).

PREREGISTERED PREDICTIONS (written before first run):
 F1 (f3 = 1, e3 = 2, NON-F2 digit): Phi3e = Phi2b^2 - 32*Phi'
   (u3 = 13, psi3 = y - eta2, irreducible, psi3(0) != 0).
   GENTOW2-A predicts: irreducible deg 8, e = 4, f = 2;
   A-route: Phi'-side (0,12)-(4,0) one-sided slope 3 = kappa2,
   on-side support {0,2,4} = supp(psi2^2 = T^4+T^2+1); Phi2b-pins
   {0:13, 2:0}; resultant v2 (x,Phi',Phi2b) = (4,12,26).
   B-route: PARI sig [(4,2)]; nfeltval triple (2,6,13).
 F2 (f3 = 2, e3 = 1, K2 = F4, digits (c1,c0) = (eta2,1)): Phi3f =
   Phi2b^2 - 4*Phi'*Phi2b - 128 (u3 = 7 > 6 = e2f2u2 floor;
   psi3 = y^2 + eta2*y + 1, NO root in F4 -> irreducible).
   GENTOW2-A predicts: irreducible deg 8, e = 2, f = 4;
   A-route: Phi'-side (0,12)-(4,0) support {0,2,4}; Phi2b-pins
   {0:14, 1:7, 2:0} ALL on side (full psi3 support); resultants
   (4,12,28). B-route: sig [(2,4)]; nfeltval (1,3,7).
 F3 (TOOTH, same polygon as F2, digit c0 flipped 1 -> eta2^2 =
   eta2+1): Phi3g = Phi2b^2 - 4*Phi'*Phi2b - 32*x*Phi' - 128
   (psi3 = y^2 + w*y + w^2 = (y+1)(y+w^2) SPLITS with DISTINCT
   roots). Thm 6.6 predicts TWO factors, each deg 4 with e = 2,
   f = 2: sig [(2,2),(2,2)] — with A-route Phi2b-pins {0:14, 1:7,
   2:0} IDENTICAL to F2's (one-sided, full support): the polygon
   cannot distinguish F2 from F3; only the K2-digit/residual can.
   Resultants still (4,12,28).
FALSIFIER: if F2 factors as [(2,2),(2,2)] (or anything but one
factor with (e,f) = (2,4)), the B-2 identification is twisted at
the F4/f3>=2 corner and GENTOW2-B's digit reading is WRONG there.
Helpers imported from gentow2_checks.py (A-route arithmetic + gp
harness); predictions here are independent hand arithmetic.
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gentow2_checks as G

PHI1 = G.PHI1
PHI2B = G.PHI2B
X = [0, 1]

PHI3E = G.padd(G.pmul(PHI2B, PHI2B), G.pmul([-32], PHI1))
PHI3F = G.padd(G.padd(G.pmul(PHI2B, PHI2B),
                      G.pmul(G.pmul([-4], PHI1), PHI2B)), [-128])
PHI3G = G.padd(PHI3F, G.pmul(G.pmul([0, -32], PHI1), [1]))

ROWS = [
    ('F1', PHI3E, {0: 13, 2: 0}, {0, 2}, 13, (4, 12, 26),
     [(4, 2)], (2, 6, 13)),
    ('F2', PHI3F, {0: 14, 1: 7, 2: 0}, {0, 1, 2}, 14, (4, 12, 28),
     [(2, 4)], (1, 3, 7)),
    ('F3', PHI3G, {0: 14, 1: 7, 2: 0}, {0, 1, 2}, 14, (4, 12, 28),
     [(2, 2), (2, 2)], None),
]


def main():
    G.say('== GENTOW2 passPE1 FRESH ROUTE (F4 x f3-boundary) ==')
    gp_jobs = []
    for tag, f, pp2, on2, h02, res, sig, tripp in ROWS:
        G.say('-- %s --' % tag)
        pins1 = G.phi_pins(list(f), PHI1, G.dv1)
        os1, J1 = G.side_check(pins1, 4, 12)
        G.chk(os1, '%s Phi-dev NOT one-sided (pins %s)' % (tag, pins1))
        G.chk(J1 == {0, 2, 4}, '%s on-side %s != {0,2,4}'
              % (tag, sorted(J1)))
        pins2 = G.phi_pins(list(f), PHI2B, G.dv2_N1)
        G.chk(pins2 == pp2, '%s Phi2b-pins %s != pred %s'
              % (tag, pins2, pp2))
        os2, J2 = G.side_check(pins2, 2, h02)
        G.chk(os2 and J2 == on2, '%s Phi2b side/support %s %s'
              % (tag, os2, sorted(J2)))
        rv = (G.v2(G.resultant(f, X)), G.v2(G.resultant(f, PHI1)),
              G.v2(G.resultant(f, PHI2B)))
        G.chk(rv == res, '%s resultant v2 %s != pred %s'
              % (tag, rv, res))
        G.say('  A-route: pins1 %s side {0,2,4}; pins2 %s; res %s'
              % (pins1, pins2, rv))
        gp_jobs.append((f, PHI2B, tripp is not None))
    G.say('== B-route (PARI/gp): %d jobs ==' % len(gp_jobs))
    sigs, trips = G.run_gp(gp_jobs)
    for i, (tag, f, pp2, on2, h02, res, sig, tripp) in enumerate(ROWS):
        G.chk(sigs.get(i) == sorted(map(tuple, sig)),
              '%s PARI sig2 %s != pred %s' % (tag, sigs.get(i), sig))
        if tripp:
            got = trips.get(i, [-1])
            G.chk(tuple(got[:3]) == tuple(tripp),
                  '%s nfeltval %s != pred %s' % (tag, got[:3], tripp))
            G.say('  %s PARI: sig %s, nfeltval=%s (e,f)=%s'
                  % (tag, sigs.get(i), got[:3], got[3:]))
        else:
            G.say('  %s PARI: sig %s (tooth: same polygon as F2, '
                  'split digit)' % (tag, sigs.get(i)))
    G.say('== FRESH-ROUTE VERDICT ==')
    G.say('checks: %d, violations: %d' % (G.NCHK[0], len(G.VIOL)))
    G.say('GENTOW2 fresh route: %s'
          % ('GREEN' if not G.VIOL else 'RED'))
    return 0 if not G.VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
