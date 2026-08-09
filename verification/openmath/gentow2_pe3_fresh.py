#!/usr/bin/env python3
"""GENTOW2 passPE3 FRESH ROUTE (hostile verifier, 2026-08-09).

Route DISJOINT from: the sealed battery (W1-W5/N1/N2), PE1's
F4 x f3 = 2 corner (F1-F3), PE2's f3 = 3 witnesses (G1-G3), and the
r2 probe LP1 (p = 2, f1 = 2, z2 = 1).  This is the record's first
letter-live contact at a DIFFERENT p (p = 3) and the FIRST frame
anywhere in the record with z2 != 1 — LP1's twist was live but its
FGMN letter landed on 1, so any formula variant with the same
exponent mod ord(z1) was indistinguishable there; here the formula's
VALUE is detectably nontrivial on both sides.

FRAMES (hand-built, p = 3; depth 2; base key x, lam1 = 1/2, e1 = 2,
h1 = 1; stage-1 key PH := x^4 + 9, N-polygon (4,0)-(0,2) slope 1/2,
residual psi1 = y^2 + 1 irreducible /F3, so f1 = 2, z1 = res(x0^2/3)
with z1^2 = -1, ord(z1) = 4 — twist exponent floor(l1*u2/e1) =
floor(11/2) = 5, z1^5 = z1 != 1: LIVE).  Stage 2: w2 = mu1(PH) = 2,
lam2 = 3/4 (h2 = 3, e2 = 2, gcd = 1), e(mu2) = 4, u2 =
e(mu2)*(w2+lam2) = 11; l1 = 1, l1' = 0 (l1*h1 + l1'*e1 = 1), pi2 =
x; letter-free normalizer at dv1-height 11 with i < e1: nhat(11) =
3^5 x = 243x (i = 1, a = 5).  Correction on-line: v3(243x) = 5 + 1/2
= 11/2 = 2*(w2+lam2).  Predicted (e, f) = (4, 2) over Q_3, single
prime.

  LV1: PHI2a := PH^2 - 243x = x^8 + 18x^4 - 243x + 81
  LV2: PHI2b := PH^2 + 243x = x^8 + 18x^4 + 243x + 81

HAND-DERIVED LETTERS (exact-algebra legs; x0 the relevant root):
  LV1: PH(x0)^2 = 243*x0 exactly, so
    eta2 = res(PH^2/(243x)) = 1                    (repo letter)
    z2   = res(PH^2/x^11) = res(243/x0^10) = z1^(-5) = z1^3 = -z1
    FORMULA: eta2 * z1^(-5) = z1^(-5) = -z1 = z2   -> holds, and
    z2 = -z1 != 1: FIRST detectably-nonzero FGMN letter.
    TOOTH LV1: eta2 = 1 != -z1 = z2 (pre-repair "eta2 <-> z2" dies
    in the direction OPPOSITE to LP1: there eta2 != 1 = z2, here
    eta2 = 1 != z2).
  LV2: PH(x0)^2 = -243*x0 exactly, so
    eta2 = res(-243x/(243x)) = -1
    z2   = res(-243/x0^10) = -z1^(-5) = -z1^3 = z1
    FORMULA: eta2 * z1^(-5) = (-1)(-z1) = z1 = z2  -> holds; BOTH
    letters differ from 1 AND from each other — the sharpest
    instance: the twist carries -1 to z1 across the F9\F3 boundary.
    TOOTH LV2: eta2 = -1 != z1 = z2.

PREREGISTERED PREDICTIONS (before the first run; no smoke run —
the first run is the sealed run).
A-route (exact integer arithmetic: this repo's pmul/padd/resultant
Bareiss harness + a LOCAL p=3 valuation vp written here; residue
facts certified by resultant valuations ONLY — no residue-field
arithmetic): with v3Res(g) := v3(Res(PHI2, g)) = 8*v(g(x0)) once the
B-route certifies a single prime:
  both frames:
    expansion identities (PHI2a/b as displayed above), and
    g = x:          v3Res = 4    (v = 1/2)
    g = PH:         v3Res = 22   (v = 11/4 = w2 + lam2, on-line)
    g = x^2 - 3:    v3Res = 8    (v = 1 exact: z1 != 1)
    g = x^2 + 3:    v3Res = 8    (v = 1 exact: z1 != -1)
    g = x^4 - 9:    v3Res = 16   (v = 2 exact: z1^2 != 1; with
                                  VPH = 22 forcing res(x0^4/9)^2 = 1
                                  it pins z1^2 = -1)
    g = x^10 - 243: v3Res = 40   (v = 5 exact: z1^5 = z1 != 1, the
                                  z2 != 1 certificate on LV1)
    g = x^12 + 729: v3Res = 62   (v = 31/4: x0^12 + 729 =
                                  PH(x0)*(PH^2 - 27PH + 243)(x0) =
                                  PH(x0)*(+-243x0 - 27PH(x0) + 243),
                                  inner min v = 5 unique at 243, so
                                  v = 11/4 + 5; > 6 certifies
                                  res(x0^12/729) = -1, which is
                                  exactly z2 = -z1 on LV1 and
                                  z2 = z1 on LV2 given the eta2
                                  exact-algebra legs)
B-route (PARI/gp: factorpadic + nfinit/idealprimedec/nfeltval +
nfmodpr residues in F9), per frame:
  NFAC 1; NPR 1; EF (4, 2); nfeltval (e = 4): VX 2, VPH 11,
  V2M3 4, V2P3 4, V4M9 8, V10 20, V12 31;
  residues: Z1NE1 1, Z1REL 1 (z1^2 + 1 == 0),
  LV1: ETA_IS_1 1, Z2_NE_1 1, Z2_IS_MZ1 1 (z2 == -z1),
       FORMULA 1 (z2 == eta2*z1^(-5)), TOOTH_ETA_NE_Z2 1
  LV2: ETA_IS_M1 1 (eta2 == -1), Z2_NE_1 1, Z2_IS_Z1 1 (z2 == z1),
       FORMULA 1, TOOTH_ETA_NE_Z2 1

Scope: like LP1 this tests the S5.1 LETTER FORMULA (and the
S2-row/S4-(c) twist propagation), NOT B-2's u == 1 residue.  The
two exact-algebra eta2 legs are BY CONSTRUCTION of the frames (the
correction term IS c*nhat(11)*x0-free...): the nontrivial machine
content is z2 (both routes) and the formula tying them.
"""
import sys
import os
import subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gentow2_checks as G

X = [0, 1]
PH = [9, 0, 0, 0, 1]                              # x^4 + 9
PHI2A = G.padd(G.pmul(PH, PH), [0, -243])         # PH^2 - 243x
PHI2B = G.padd(G.pmul(PH, PH), [0, 243])          # PH^2 + 243x


def vp(n, p=3):
    n = abs(n)
    assert n != 0
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


GP_PROG = r"""
default(parisize, 64000000);
{FRAMES = [
 ["LV1", x^8 + 18*x^4 - 243*x + 81],
 ["LV2", x^8 + 18*x^4 + 243*x + 81]];
PH = x^4 + 9;
for(t = 1, 2,
  tag = FRAMES[t][1]; F = FRAMES[t][2];
  print(tag, " NFAC ", matsize(factorpadic(F, 3, 60))[1]);
  K = nfinit(F);
  dec = idealprimedec(K, 3);
  print(tag, " NPR ", length(dec));
  pr = dec[1];
  print(tag, " EF ", pr.e, " ", pr.f);
  print(tag, " VX ", nfeltval(K, x, pr));
  print(tag, " VPH ", nfeltval(K, PH, pr));
  print(tag, " V2M3 ", nfeltval(K, x^2 - 3, pr));
  print(tag, " V2P3 ", nfeltval(K, x^2 + 3, pr));
  print(tag, " V4M9 ", nfeltval(K, x^4 - 9, pr));
  print(tag, " V10 ", nfeltval(K, x^10 - 243, pr));
  print(tag, " V12 ", nfeltval(K, x^12 + 729, pr));
  z1 = nfmodpr(K, Mod(x, F)^2 / 3, pr);
  e2 = nfmodpr(K, Mod(PH, F)^2 / (243*Mod(x, F)), pr);
  z2 = nfmodpr(K, Mod(PH, F)^2 / Mod(x, F)^11, pr);
  print(tag, " Z1NE1 ", z1 != 1);
  print(tag, " Z1REL ", z1^2 + 1 == 0);
  if(t == 1, print(tag, " ETA_IS_1 ", e2 == 1),
             print(tag, " ETA_IS_M1 ", e2 == -1));
  print(tag, " Z2_NE_1 ", z2 != 1);
  if(t == 1, print(tag, " Z2_IS_MZ1 ", z2 == -z1),
             print(tag, " Z2_IS_Z1 ", z2 == z1));
  print(tag, " FORMULA ", z2 == e2 * z1^(-5));
  print(tag, " TOOTH_ETA_NE_Z2 ", e2 != z2));}
quit
"""

B_PRED = {}
for _tag in ('LV1', 'LV2'):
    B_PRED.update({_tag + ' NFAC': '1', _tag + ' NPR': '1',
                   _tag + ' EF': '4 2', _tag + ' VX': '2',
                   _tag + ' VPH': '11', _tag + ' V2M3': '4',
                   _tag + ' V2P3': '4', _tag + ' V4M9': '8',
                   _tag + ' V10': '20', _tag + ' V12': '31',
                   _tag + ' Z1NE1': '1', _tag + ' Z1REL': '1',
                   _tag + ' Z2_NE_1': '1', _tag + ' FORMULA': '1',
                   _tag + ' TOOTH_ETA_NE_Z2': '1'})
B_PRED['LV1 ETA_IS_1'] = '1'
B_PRED['LV1 Z2_IS_MZ1'] = '1'
B_PRED['LV2 ETA_IS_M1'] = '1'
B_PRED['LV2 Z2_IS_Z1'] = '1'

A_RES_PRED = (('x', X, 4), ('PH', PH, 22), ('x^2-3', [-3, 0, 1], 8),
              ('x^2+3', [3, 0, 1], 8),
              ('x^4-9', [-9, 0, 0, 0, 1], 16),
              ('x^10-243', [-243] + [0] * 9 + [1], 40),
              ('x^12+729', [729] + [0] * 11 + [1], 62))


def main():
    G.say('== GENTOW2 passPE3 FRESH ROUTE (p = 3 letter-live, '
          'z2 != 1: frames LV1/LV2) ==')
    G.say('-- A-route (exact integer arithmetic, local v3) --')
    G.chk(PHI2A == [81, -243, 0, 0, 18, 0, 0, 0, 1],
          'PHI2A expansion mismatch')
    G.chk(PHI2B == [81, 243, 0, 0, 18, 0, 0, 0, 1],
          'PHI2B expansion mismatch')
    for ftag, F in (('LV1', PHI2A), ('LV2', PHI2B)):
        for tag, g, pred in A_RES_PRED:
            got = vp(G.resultant(F, g))
            G.chk(got == pred, '%s v3 Res(PHI2, %s) = %s != pred %s'
                  % (ftag, tag, got, pred))
            G.say('  %s v3 Res(PHI2, %s) = %s' % (ftag, tag, got))
    G.say('-- B-route (PARI/gp: nfmodpr residues in F9) --')
    out = subprocess.run(['gp', '-q', '-f'], input=GP_PROG,
                         capture_output=True, text=True, timeout=900)
    got = {}
    for line in out.stdout.splitlines():
        parts = line.strip().split(None, 2)
        if len(parts) == 3 and (parts[0] + ' ' + parts[1]) in B_PRED:
            got[parts[0] + ' ' + parts[1]] = ' '.join(parts[2].split())
    if out.stderr.strip():
        G.say('  gp stderr tail: %s' % out.stderr[-300:])
    for key in sorted(B_PRED):
        G.chk(got.get(key) == B_PRED[key],
              'B-route %s = %r != pred %r'
              % (key, got.get(key), B_PRED[key]))
        G.say('  %s: got %s (pred %s)' % (key, got.get(key),
                                          B_PRED[key]))
    G.say('== passPE3 FRESH-ROUTE VERDICT ==')
    G.say('checks: %d, violations: %d' % (G.NCHK[0], len(G.VIOL)))
    for vmsg in G.VIOL:
        G.say('VIOLATION: %s' % vmsg)
    G.say('GENTOW2 passPE3 fresh route: %s'
          % ('GREEN' if not G.VIOL else 'RED'))
    return 0 if not G.VIOL else 1


if __name__ == '__main__':
    sys.exit(main())
