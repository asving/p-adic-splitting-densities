#!/usr/bin/env python3
"""GENTOW2 r2 LETTER-LIVE PROBE (PE2 F1 repair round, 2026-08-09).

First letter-live (f1 >= 2) machine contact for the GENTOW2 record:
the 13 witnesses standing at PE2 (battery W1-W5/N1/N2 + PE1 F1-F3 +
PE2 G1-G3) each sit at f1 = 1 over q = 2, forcing z1 = 1 — the
letter-twist face of the S5.1 LETTER FORMULA

    z2 = eta2 * z1^(-floor(l1*u2/e1))

was machine-untested (the PE2 report's disclosed PE3 fresh-route
need). This probe tests the formula at ONE frame where the twist is
LIVE (z1 in F4 minus F2, twist exponent not divisible by ord(z1)),
and its TOOTH is the pre-repair identification itself: "eta2 <-> z2"
must FAIL (eta2 != z2) at this frame.

FRAME LP1 (hand-built, p = 2): base key x, lam1 = 1/2 (e1 = 2,
h1 = 1); stage-1 residual psi1 = y^2 + y + 1 (f1 = 2), realized by
the stage-1 key PH := x^4 + 2x^2 + 4 (N-polygon (4,0)-(0,2) slope
1/2, residual y^2+y+1 irreducible /F2; z1 = res(x^2/2), z1^2 + z1 +
1 = 0). Depth-2 key PHI2 := PH^2 - 8x^3 (e2 = 2, f2 = 1: w2 = 2,
lam2 = 1/4, on-line since v(8x^3) = 9/2 = 2*(w2+lam2)); deg 8,
predicted (e, f) = (4, 2) over Q_2. FGMN chain data at the leaf
x0 (a PHI2-root): e(mu2) = 4, u2 = e(mu2)*(w2+lam2) = 9, l1 = 1,
l1' = 0 (l1*h1 + l1'*e1 = 1), pi2 = x, gamma2 = PH^2 * x^(-9)
(Def 3.12); letter-free normalizer at dv1-height 9 with i < e1:
nhat(9) = 16x (i = 1, a = 4) — the S5.1/T(b)'(i) normal form.

HAND-DERIVED VALUES (before the run; exact-algebra legs shown):
  PH(x0)^2 = 8*x0^3 exactly (PHI2(x0) = 0), so
  eta2 = res(PH^2/(16x)) = res(x0^2/2) = z1        (repo letter)
  z2   = res(PH^2/x^9)  = res(8/x0^6) = z1^(-3) = 1 (FGMN letter)
  floor(l1*u2/e1) = floor(9/2) = 4:
  eta2 * z1^(-4) = z1^(-3) = 1 = z2  -> FORMULA holds, twist LIVE
  (z1^4 = z1 != 1), and eta2 = z1 != 1 = z2 -> TOOTH fires against
  the pre-repair "eta2 <-> z2". FGMN psi2 = y - 1 differs from the
  repo psi2 = y - z1: the S2-row/S4-(c) twist is material here.

PREREGISTERED PREDICTIONS.
A-route (this repo's exact integer arithmetic, decorrelated from
PARI): polynomial identities PHI2 = PH^2 - 8x^3 and x^6 - 8 =
(x^2 - 2)*PH (the second proves res(x0^6/8) = 1, i.e. z1^3 = 1 and
z2 = 1, by exact algebra + one valuation); v2 of Res(PHI2, g) =
8 * v(g(x0)) [single prime above 2, so conjugates share v]:
  g = x:        v2Res = 4   (v = 1/2)
  g = PH:       v2Res = 18  (v = 9/4 = w2 + lam2)
  g = x^2 - 2:  v2Res = 8   (v = 1: x0^2 = 2*(z1-unit), z1 != 1)
  g = x^6 - 8:  v2Res = 26  (v = 13/4 = 1 + 9/4, the identity leg)
  g = x^8 - 16: v2Res = 32  (v = 4: res(x0^8/16) = z1^4 = z1 != 1,
                             so x^8 - 16 has the value of 16)
The (4, 26, 32) triple certifies z1 != 1, z1^3 = 1 (=> z2 = 1),
eta2 != z2 with NO residue-field arithmetic.
B-route (PARI/gp: factorpadic + nfinit/idealprimedec/nfeltval +
nfmodpr in F4): NFAC 1; NPR 1; EF (4, 2); nfeltval: VX 2, VPH 9,
V22 4, V68 13, V816 16 (pr-units, e = 4); residues: Z1NE1 True,
Z1REL True (z1^2+z1+1 = 0), ETA_IS_Z1 True, Z2_IS_1 True,
FORMULA True (z2 == eta2*z1^(-4)), TOOTH_ETA_NE_Z2 True.

Scope: this probe tests the LETTER FORMULA (S5.1 [r2]), NOT B-2's
u == 1 residue — the B-2 machine support stays as recorded in the
honesty box. Smoke record: none (first run is the sealed run).
"""
import sys
import os
import subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gentow2_checks as G

X = [0, 1]
PH = [4, 0, 2, 0, 1]                      # x^4 + 2x^2 + 4
PHI2 = G.padd(G.pmul(PH, PH), [0, 0, 0, -8])   # PH^2 - 8x^3

GP_PROG = r"""
default(parisize, 64000000);
F2 = x^8 + 4*x^6 + 12*x^4 - 8*x^3 + 16*x^2 + 16;
PH = x^4 + 2*x^2 + 4;
print("NFAC ", matsize(factorpadic(F2, 2, 60))[1]);
K = nfinit(F2);
dec = idealprimedec(K, 2);
print("NPR ", length(dec));
pr = dec[1];
print("EF ", pr.e, " ", pr.f);
print("VX ", nfeltval(K, x, pr));
print("VPH ", nfeltval(K, PH, pr));
print("V22 ", nfeltval(K, x^2 - 2, pr));
print("V68 ", nfeltval(K, x^6 - 8, pr));
print("V816 ", nfeltval(K, x^8 - 16, pr));
z1 = nfmodpr(K, Mod(x, F2)^2 / 2, pr);
e2 = nfmodpr(K, Mod(PH, F2)^2 / (16*Mod(x, F2)), pr);
z2 = nfmodpr(K, Mod(PH, F2)^2 / Mod(x, F2)^9, pr);
print("Z1NE1 ", z1 != 1);
print("Z1REL ", z1^2 + z1 + 1 == 0);
print("ETA_IS_Z1 ", e2 == z1);
print("Z2_IS_1 ", z2 == 1);
print("FORMULA ", z2 == e2 * z1^(-4));
print("TOOTH_ETA_NE_Z2 ", e2 != z2);
quit
"""

B_PRED = {'NFAC': '1', 'NPR': '1', 'EF': '4 2', 'VX': '2',
          'VPH': '9', 'V22': '4', 'V68': '13', 'V816': '16',
          'Z1NE1': '1', 'Z1REL': '1', 'ETA_IS_Z1': '1',
          'Z2_IS_1': '1', 'FORMULA': '1', 'TOOTH_ETA_NE_Z2': '1'}


def main():
    G.say('== GENTOW2 r2 LETTER-LIVE PROBE (frame LP1: f1 = 2, '
          'z1 in F4\\F2) ==')
    G.say('-- A-route (exact integer arithmetic) --')
    lhs = [-8, 0, 0, 0, 0, 0, 1]                     # x^6 - 8
    rhs = G.pmul([-2, 0, 1], PH)                     # (x^2-2)*PH
    G.chk(lhs == rhs, 'identity x^6 - 8 != (x^2 - 2)*PH')
    G.chk(PHI2 == [16, 0, 16, -8, 12, 0, 4, 0, 1],
          'PHI2 expansion mismatch')
    for tag, g, pred in (('x', X, 4), ('PH', PH, 18),
                         (('x^2-2'), [-2, 0, 1], 8),
                         (('x^6-8'), lhs, 26),
                         (('x^8-16'), [-16, 0, 0, 0, 0, 0, 0, 0, 1],
                          32)):
        got = G.v2(G.resultant(PHI2, g))
        G.chk(got == pred, 'v2 Res(PHI2, %s) = %s != pred %s'
              % (tag, got, pred))
        G.say('  v2 Res(PHI2, %s) = %s' % (tag, got))
    G.say('-- B-route (PARI/gp: nfmodpr residues in F4) --')
    out = subprocess.run(['gp', '-q', '-f'], input=GP_PROG,
                         capture_output=True, text=True, timeout=600)
    got = {}
    for line in out.stdout.splitlines():
        parts = line.strip().split(None, 1)
        if len(parts) == 2 and parts[0] in B_PRED:
            got[parts[0]] = ' '.join(parts[1].split())
    if out.stderr.strip():
        G.say('  gp stderr tail: %s' % out.stderr[-300:])
    for key in B_PRED:
        G.chk(got.get(key) == B_PRED[key], 'B-route %s = %r != pred %r'
              % (key, got.get(key), B_PRED[key]))
        G.say('  %s: got %s (pred %s)' % (key, got.get(key),
                                          B_PRED[key]))
    G.say('== r2 LETTER-PROBE VERDICT ==')
    G.say('checks: %d, violations: %d' % (G.NCHK[0], len(G.VIOL)))
    for vmsg in G.VIOL:
        G.say('VIOLATION: %s' % vmsg)
    G.say('GENTOW2 r2 letter probe: %s'
          % ('GREEN' if not G.VIOL else 'RED'))
    return 0 if not G.VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
