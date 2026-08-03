#!/usr/bin/env python3
# level3_xcheck_liftdev.py -- M5 post-seal diagnostic (NON-PREREG): characterize the
# plain-lift vs canonical-corrected-lift cocycle deviation found by level3_xcheck_compare
# (LEG-P). Prints, per diverging tower, the deviation factor c3_plain/c3_canonical
# bucketed by (factor, d3, d2, d1, D2). Finding: factor == eps1(gamma2), exactly at d2=1.
import sys, os
sys.path.insert(0, '/data/users/asvin/math-and-lean/p-adic-splitting-densities/verification/openmath')
import level3_xcheck as MX
import iterlawr_probe as ILP
from iterlawr_probe import Composite3
from strata3_probe import Tower3

def convT2M(level, x):
    if level == 0: return x[0]
    return tuple(convT2M(level - 1, c) for c in x)
def convM2T(level, x):
    if level == 0: return (x,)
    return tuple(convM2T(level - 1, c) for c in x)
def conv_psi(level, psi):
    return [convT2M(level, c) for c in psi[:-1]]

for kind, p in ILP.CONFIGS:
    for tag, d0, r0, r1, r2 in ILP.ROWS:
        if d0 != 1: continue
        full = f"{kind},p={p},{tag}"
        T3 = Tower3(kind, p, d0, r0, r1, r2, full)
        C = Composite3(T3)
        E3 = T3.E3
        W1 = list(range(C.Gamma0, C.Gamma0 + E3))
        R = MX.ZRing(p) if kind == "Zp" else MX.TRing(p)
        reads = [(r0[0], r0[1], conv_psi(0, T3.T.psi0)),
                 (r1[0], r1[1], conv_psi(1, T3.T.psi1)),
                 (r2[0], r2[1], conv_psi(2, T3.psi2))]
        Tp = MX.Tower(R, reads)
        if Tp.Phi[2] == list(T3.T.Phi2): continue
        K3 = C.K3
        devs = {}
        for ga in W1:
            for gb in W1:
                ct = C.cocycle(ga, gb)[0]
                cp, diag = Tp.cocycle(ga, gb)
                cpt = convM2T(3, cp)
                if cpt == ct: continue
                fac = K3["mul"](cpt, K3["inv"](ct))
                # constants for this pair
                cst = C.constants(ga, gb)
                s = ILP.k3_repr(C, fac)
                key = (s, cst['d3'], cst['d2'], cst['d1'], cst['D2'])
                devs[key] = devs.get(key, 0) + 1
        if devs:
            print(full, "g1=", r1[2], "deviations (factor, d3,d2,d1,D2): ")
            for k, v in sorted(devs.items()):
                print("   ", k, "x", v)
