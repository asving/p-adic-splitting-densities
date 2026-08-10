#!/usr/bin/env python3
"""GENTOW2 passPE4 DECODE PROBE (2026-08-10) — sealed AFTER the fresh
runner's first-run-under-seal came back RED 62/9 (disclosed: these
predictions are derived post-hoc from that run's failure pattern, then
sealed before THIS probe's first run).

The sealed runner (gentow2_pe4_fresh.py, seal 23def87) found: LD2
(per-height digit string (z1, z1^2), prescribed psi3 = y^2+z1*y+z1^2
SPLIT) is (4,4) SINGLE prime — the per-height digit string does NOT
spell the realized residual: B-2 (u == 1) fails at letter-live grades.

HAND DECODE (division identity at a PHI3-root xi, N := nhat2(19)(xi)
= 4*xi*PHIP(xi), r3 := res(PHI2(xi)/N), r1 := res(xi^2/2),
eta2read := res(PHIP^2/(16xi)) = r1):
  PHI2^2 = k1*PHI2 + k0 at xi  ==>  r3^2 = res(k1/N)*r3 + res(k0/N^2).
  res(k1/N) = res(xi^2/2) = r1 (t = 1: multiplicative = per-height).
  LD1 k0 = 512x:        res(k0/N^2) = res(32/(xi*PHIP^2))
      = res(16xi/PHIP^2)*res(2/xi^2) = r1^(-1)*r1^(-1) = r1.
  LD2 k0 = 256x^3+512x: res(k0/N^2) = r1^2*(1 + r1^2) = r1^2*r1 = 1.
  COCYCLE: res(N^2/nhat2(38)) = res(16xi^2 PHIP^2/(512xi))
      = res(PHIP^2/(16xi))*res(xi^2/2) = r1*r1 = r1^2 = r1 + 1.
So the REALIZED residuals (in the y = PHI2/nhat2(19)-read frame):
  LD1: y^2 + r1*y + r1   (irreducible /F4: t^2+t+z1^2 after y = z1*t,
       Tr(z1^2) = 1) — consistent with the machine (4,4);
  LD2: y^2 + r1*y + 1    (irreducible — LD1's ORIGINALLY prescribed
       psi3!) — consistent with the machine (4,4).
i.e. realized = y^2 + c1*y + z1*c0: the grade-38 slot carries the
extra letter factor z1 = the per-height/multiplicative normalizer
cocycle res(nhat2(38)/nhat2(19)^2) — GENTOW2-B'(5)'s u(beta_t) with
u(19-grade) = 1, u(38-grade) = z1 in this frame: grade-varying,
z1-valued, identically 1 on letter-dead geography (all 13 standing
witnesses) — the theta-cocycle mode the note's fallback clause names.

PREREGISTERED PREDICTIONS for THIS probe (each per single prime,
PARI nfmodpr in F16):
  LD1: MP  r3^2 + r1*r3 + r1 == 0;  DEEP r3^4 != r3;
       MULT1 res(k1/N) == r1;  MULT0 res(k0/N^2) == r1;
       COC res(N^2/(512*xi)) == r1 + 1.
  LD2: MP  r3^2 + r1*r3 + 1 == 0;  DEEP r3^4 != r3;
       MULT1 == r1;  MULT0 res((256xi^3+512xi)/N^2) == 1;
       COC == r1 + 1.
"""

import subprocess, sys

def norm(p):
    while p and p[-1] == 0: p.pop()
    return p

def pmul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, ca in enumerate(a):
        if ca:
            for j, cb in enumerate(b): r[i+j] += ca*cb
    return norm(r)

def padd(a, b):
    r = [0]*max(len(a), len(b))
    for i, c in enumerate(a): r[i] += c
    for i, c in enumerate(b): r[i] += c
    return norm(r)

def gsub(a, b): return padd(a, [-c for c in b])

GP = r"""
default(parisize, 256000000);
probe(tag, F, PHIP, PHI2, K0) = {
  my(K, pr, xF, N, r1, r3, m1, m0, coc);
  K = nfinit([F, [2]]);
  pr = idealprimedec(K, 2)[1];
  xF = Mod(x, F);
  N = 4*xF*Mod(PHIP, F);
  r1 = nfmodpr(K, xF^2/2, pr);
  r3 = nfmodpr(K, Mod(PHI2, F)/N, pr);
  m1 = nfmodpr(K, Mod(2*x^3, F)*Mod(PHIP, F)/N, pr);
  m0 = nfmodpr(K, Mod(K0, F)/N^2, pr);
  coc = nfmodpr(K, N^2/(512*xF), pr);
  print(tag, " MP1 ", r3^2 + r1*r3 + r1 == 0);
  print(tag, " MP2 ", r3^2 + r1*r3 + 1 == 0);
  print(tag, " DEEP ", r3^4 != r3);
  print(tag, " MULT1 ", m1 == r1);
  print(tag, " MULT0R1 ", m0 == r1);
  print(tag, " MULT0ONE ", m0 == 1);
  print(tag, " COC ", coc == r1 + 1);
}
"""

def main():
    PHIP = [4, 0, 2, 0, 1]
    PHI2 = gsub(pmul(PHIP, PHIP), [0, 0, 0, 8])
    k1 = pmul([0, 0, 0, 2], PHIP)
    LD1 = gsub(gsub(pmul(PHI2, PHI2), pmul(k1, PHI2)), [0, 512])
    LD2 = gsub(gsub(pmul(PHI2, PHI2), pmul(k1, PHI2)), [0, 512, 0, 256])
    lit = lambda p: 'Pol(%s)' % list(reversed(p))
    prog = GP
    prog += 'probe("LD1", %s, %s, %s, %s);\n' % (lit(LD1), lit(PHIP), lit(PHI2), lit([0, 512]))
    prog += 'probe("LD2", %s, %s, %s, %s);\n' % (lit(LD2), lit(PHIP), lit(PHI2), lit([0, 512, 0, 256]))
    out = subprocess.run(['gp', '-q', '-f'], input=prog, capture_output=True, text=True, timeout=600)
    lines = [l.strip() for l in out.stdout.splitlines() if l.strip()]
    for l in lines: print(' ', l)
    if out.stderr.strip(): print('gp stderr:', out.stderr.strip()[:400])
    has = lambda s: any(l == s for l in lines)
    exp = ['LD1 MP1 1', 'LD1 MP2 0', 'LD1 DEEP 1', 'LD1 MULT1 1', 'LD1 MULT0R1 1',
           'LD1 MULT0ONE 0', 'LD1 COC 1',
           'LD2 MP1 0', 'LD2 MP2 1', 'LD2 DEEP 1', 'LD2 MULT1 1', 'LD2 MULT0R1 0',
           'LD2 MULT0ONE 1', 'LD2 COC 1']
    bad = [s for s in exp if not has(s)]
    for s in bad: print('VIOLATION:', s)
    print('== passPE4 DECODE VERDICT ==')
    print('checks: %d, violations: %d' % (len(exp), len(bad)))
    print('GENTOW2 passPE4 decode: %s' % ('GREEN' if not bad else 'RED'))
    return len(bad)

if __name__ == '__main__':
    sys.exit(1 if main() else 0)
