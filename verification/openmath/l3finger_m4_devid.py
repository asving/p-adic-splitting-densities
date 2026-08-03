#!/usr/bin/env python3
"""l3finger_m4_devid.py — M4 fingerprint SUPPLEMENT (post-seal, non-prereg).

The inflation-defect identity: on every W1xW1 pair of the M4 fresh roster,
the deviation of the zbar-stripped measured level-3 cocycle from the MEASURED
level-2 shadow cocycle at (beta2, beta2') equals EXACTLY

    dev == z2^(D2 - d2) * z1^(D1 - Ds),

where (D2, D1) are the sealed composed constants of the pair and (d2, Ds) are
the ACCEPTED level-2 law constants of the shadow pair (b2a, b2b):
d2 = floor((s2+s2')/e1), Ds = (s1(b2a-chain) + s1(b2b-chain) - s1(split of
b2a+b2b) + l0*gamma2*d2)/e0.  Field-level check, all 44 towers.
"""
import sys, os, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import iterlawr_probe as IP
from iterlawr_probe import Composite3
from strata3_probe import Tower3
import strata_probe as SP
from grb_order2_check import eq12
from l3finger_m4 import ROWS, CONFIGS

tot = viol = l2win = nonint = 0
for kind, p in CONFIGS:
    for tag, d0, r0, r1, r2 in ROWS:
        full = f"{kind},p={p},{tag}"
        T3 = Tower3(kind, p, d0, r0, r1, r2, full)
        T = T3.T
        C = Composite3(T3)
        K3, E3 = C.K3, T3.E3
        C2 = SP.Composite(T)
        W1 = list(range(C.Gamma0, C.Gamma0 + E3))
        for ga in W1:
            for gb in W1:
                s3a, s2a, s1a, b2a, b1a, _ = C.split(ga)
                s3b, s2b, s1b, b2b, b1b, _ = C.split(gb)
                cst = C.constants(ga, gb)
                try:
                    c2v = C2.cocycle(b2a, b2b)[0]
                except AssertionError:
                    l2win += 1; continue
                cval, _, nz, _ = C.cocycle(ga, gb)
                j = nz[0]
                body = K3["mul"](cval, K3["inv"](K3["pow"](C.zbar, j)))
                dev = K3["mul"](body, K3["inv"](K3["embed"](c2v)))
                # shadow constants (accepted level-2 law on the b2 pair)
                d2 = cst["d2"]                      # floor((s2a+s2b)/e1)
                s1s = eq12(eq12(b2a + b2b, T.e1, T.h1)[1]
                           - eq12(b2a + b2b, T.e1, T.h1)[0]*T.w1Phi1,
                           T.e0, T.h0)[0]
                numS = s1a + s1b - s1s + T.l0*T.gamma2*d2
                tot += 1
                if numS % T.e0 or cst["D2"] is None or cst["D1"] is None:
                    nonint += 1
                    print(f"NONINT {full} ({ga},{gb})")
                    continue
                Ds = numS // T.e0
                pred = K3["mul"](K3["pow"](C.z2_3, cst["D2"] - d2),
                                 K3["pow"](C.z1_3, cst["D1"] - Ds))
                if dev != pred:
                    viol += 1
                    print(f"VIOL {full} ({ga},{gb})")
print(f"INFLATION-DEFECT IDENTITY: {viol} violations / {tot} pairs "
      f"(shadow nonintegral: {nonint}; L2-window misses: {l2win})")
sys.exit(0 if viol == 0 and nonint == 0 else 1)
