#!/usr/bin/env python3
"""GENTOW2 passPE2 FRESH ROUTE (hostile verifier, 2026-08-09).

Route DISJOINT from the sealed battery (W1-W5/N1/N2, f3 <= 2) and
from PE1's fresh F1-F3 (f3 <= 2): the FIRST f3 = 3 witnesses
anywhere — three K2-digit slots at three distinct Gamma_2 grades,
and the first side whose psi2-power residual support is NOT full
(supp(psi2^3) = {0,1,3,5,6}: interior abscissas 2 and 4 must sit
STRICTLY ABOVE the side — a sharper clause-(c) prediction than any
committed witness, where supports were full or even-spaced).

Tower: the N1 frame of gentow2_checks.py (Phi' = x^2-2, Phi2b =
Phi'^2 - 2x*Phi' - 8; e1=2 f1=1 h=1, e2=1 f2=2, u2=3,
psi2 = T^2+T+1, K2 = F4 = F2(w), w = eta2 = class(Phi'(xi)/2x(xi)),
dv2(pi^a x^i Phi'^b) = 2a + i + 3b). Third stage: e3 = 1, f3 = 3,
u3 = kappa3 = 7 > 6 = e2f2u2 (floor OK, lam3 > 0), deg Phi3 =
e3*f3*deg(Phi2b) = 12. Digit lifts (hand-derived, independent leg:
class(4Phi'@7) = class(32xPhi'@14) = class(512Phi'@21) = eta2 via
res(Phi'/2x) = eta2 and res(x^2/2) = 1; normalizers 8x@7, 128@14,
1024x@21 class 1). Recipe: Phi3 = Phi2b^3 - k1*Phi2b - k0 etc.

PREREGISTERED PREDICTIONS (hand-derived from GENTOW2-A/B + FGMN
Cor 6.4 BEFORE the first run; independent of the note's authors):
 G1: psi3 = y^3 + w*y + 1 (no F4 root -> irreducible; psi3(0)!=0):
   Phi3 = Phi2b^3 - 32*x*Phi'*Phi2b - 1024*x  (c2,c1,c0)=(0,w,1).
   A-route: Phi'-dev one-sided (0,18)-(6,0) slope 3 = kappa2,
   on-side support = supp(psi2^3 = T^6+T^5+T^3+T+1) = {0,1,3,5,6}
   (j = 2,4 strictly above); Phi2b-pins {0:21, 1:14, 3:0} all on
   side (0,21)-(3,0) slope 7 = kappa3, support {0,1,3} = supp(psi3);
   resultant v2 (x, Phi', Phi2b) = (6, 18, 42) [= 12*(1/2, 3/2, 7/2)].
   B-route: irreducible, sig [(2,6)] (e = e1e2e3 = 2, f = f1f2f3 = 6),
   nfeltval triple (1, 3, 7) [= 2*(1/2, 3/2, 7/2)].
 G2: psi3 = y^3 + w*y^2 + 1 (no F4 root -> irreducible; first
   witness anywhere with a nonzero y^2-digit at f3 = 3):
   Phi3 = Phi2b^3 - 4*Phi'*Phi2b^2 - 1024*x  (c2,c1,c0)=(w,0,1).
   A-route: same Phi'-side data as G1; Phi2b-pins {0:21, 2:7, 3:0}
   on side, support {0,2,3} = supp(psi3); resultants (6,18,42).
   B-route: sig [(2,6)], nfeltval (1,3,7).
 G3 (TOOTH): psi3 = y^3 + w*y + w = (y+w)(y^2+w*y+1), SPLIT into
   distinct irreducible factors (deg 1 + deg 2 over F4):
   Phi3 = Phi2b^3 - 32*x*Phi'*Phi2b - 512*Phi'  (c0 flipped 1 -> w).
   A-route: Phi2b-pins {0:21, 1:14, 3:0} IDENTICAL to G1 (one-sided,
   same support {0,1,3}), Phi'-side data IDENTICAL to G1 (residual
   R2 = psi2^1 * psi2^2 = psi2^3, same support) — NO polygon or
   support datum separates G3 from G1; only the K2-digit string
   does. B-route MUST return sig [(2,2),(2,4)] (Thm 6.6: one factor
   per residual factor: linear -> deg 4 (2,2); quadratic -> deg 8
   (2,4)). Resultants still (6,18,42).
FALSIFIER: G1 or G2 not [(2,6)] (or wrong triple/pins/support), or
G3 = [(2,6)] — then the GENTOW2-A/B digit reading is WRONG at the
never-witnessed f3 = 3 branch and the note's clause (c)/(e) or the
B-2 residue fails there.
Helpers imported from gentow2_checks.py (A-route integer arithmetic
+ gp harness); all predictions here are independent hand arithmetic
(this docstring written and sealed before the first run).
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gentow2_checks as G

PHI1 = G.PHI1
PHI2B = G.PHI2B
X = [0, 1]

P2SQ = G.pmul(PHI2B, PHI2B)
P2CU = G.pmul(P2SQ, PHI2B)

G1 = G.padd(G.padd(P2CU, G.pmul(G.pmul([0, -32], PHI1), PHI2B)),
            [0, -1024])
G2 = G.padd(G.padd(P2CU, G.pmul(G.pmul([-4], PHI1), P2SQ)),
            [0, -1024])
G3 = G.padd(G.padd(P2CU, G.pmul(G.pmul([0, -32], PHI1), PHI2B)),
            G.pmul([-512], PHI1))

ONSIDE1 = {0, 1, 3, 5, 6}          # supp(psi2^3), j=2,4 strictly above

ROWS = [
    ('G1', G1, {0: 21, 1: 14, 3: 0}, {0, 1, 3}, 21, (6, 18, 42),
     [(2, 6)], (1, 3, 7)),
    ('G2', G2, {0: 21, 2: 7, 3: 0}, {0, 2, 3}, 21, (6, 18, 42),
     [(2, 6)], (1, 3, 7)),
    ('G3', G3, {0: 21, 1: 14, 3: 0}, {0, 1, 3}, 21, (6, 18, 42),
     [(2, 2), (2, 4)], None),
]


def main():
    G.say('== GENTOW2 passPE2 FRESH ROUTE (first f3 = 3 witnesses) ==')
    gp_jobs = []
    for tag, f, pp2, on2, h02, res, sig, tripp in ROWS:
        G.say('-- %s --' % tag)
        pins1 = G.phi_pins(list(f), PHI1, G.dv1)
        os1, J1 = G.side_check(pins1, 6, 18)
        G.chk(os1, '%s Phi-dev NOT one-sided (pins %s)' % (tag, pins1))
        G.chk(J1 == ONSIDE1, '%s on-side %s != supp(psi2^3) %s'
              % (tag, sorted(J1), sorted(ONSIDE1)))
        pins2 = G.phi_pins(list(f), PHI2B, G.dv2_N1)
        G.chk(pins2 == pp2, '%s Phi2b-pins %s != pred %s'
              % (tag, pins2, pp2))
        os2, J2 = G.side_check(pins2, 3, h02)
        G.chk(os2 and J2 == on2, '%s Phi2b side/support %s %s'
              % (tag, os2, sorted(J2)))
        rv = (G.v2(G.resultant(f, X)), G.v2(G.resultant(f, PHI1)),
              G.v2(G.resultant(f, PHI2B)))
        G.chk(rv == res, '%s resultant v2 %s != pred %s'
              % (tag, rv, res))
        G.say('  A-route: pins1 %s side %s; pins2 %s; res %s'
              % (pins1, sorted(J1), pins2, rv))
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
            G.chk(tuple(got[3:]) == (2, 6),
                  '%s (e,f) %s != (2,6)' % (tag, got[3:]))
            G.say('  %s PARI: sig %s, nfeltval=%s (e,f)=%s'
                  % (tag, sigs.get(i), got[:3], got[3:]))
        else:
            G.say('  %s PARI: sig %s (tooth: polygon+support identical '
                  'to G1, digit c0 flipped)' % (tag, sigs.get(i)))
    G.say('== PE2 FRESH-ROUTE VERDICT ==')
    G.say('checks: %d, violations: %d' % (G.NCHK[0], len(G.VIOL)))
    for vmsg in G.VIOL:
        G.say('VIOLATION: %s' % vmsg)
    G.say('GENTOW2 PE2 fresh route: %s'
          % ('GREEN' if not G.VIOL else 'RED'))
    return 0 if not G.VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
