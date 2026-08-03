#!/usr/bin/env python3
"""strata3e2_design.py — DESIGN-TIME tower-constant table for the TWIST-3
probe (synthesis-7 queue #5).  Computes, per candidate roster row x ring:
theta2 = l1*g1*gamma2, ord(z2) in K2, and twist VISIBILITY (z2^theta2 != 1)
— the G2 lesson (small-field towers are twist-blind) applied at level 2.
NO C^F3/c^G3 comparison is computed here: tower constants only (the same
design work as the parents' "designed rows ... chosen multiplicatively
rich").  Construction itself exercises build_Phi3/realize2 at e1 >= 2
(a crash here = infeasible row, redesign BEFORE sealing)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import strata3_probe as S3

CAND = [
    ("R2A", 1, (1,1,2), (2,1,1), (1,1,2)),
    ("R2B", 1, (1,1,2), (2,3,1), (1,3,3)),
    ("R2C", 1, (1,1,1), (2,1,2), (1,1,2)),
    ("R2D", 2, (1,1,1), (2,1,2), (1,1,1)),
    ("R2E", 1, (1,1,2), (3,1,1), (1,1,2)),
    ("R2F", 1, (1,1,1), (3,2,2), (1,1,1)),
]

def ordmul(K, x):
    if K["isz"](x): return None
    n = 1; y = x
    while y != K["one"]:
        y = K["mul"](y, x); n += 1
        if n > 10**6: return -1
    return n

for kind, p in [("Zp",2),("Zp",3),("Fpt",2),("Fpt",3)]:
    for tag, d0, r0, r1, r2 in CAND:
        T3 = S3.Tower3(kind, p, d0, r0, r1, r2, f"{kind},p={p},{tag}")
        T = T3.T
        theta2 = T.l1 * T.g1 * T.gamma2
        oz = ordmul(T3.K2, T3.z2)
        vis = T3.K2["pow"](T3.z2, theta2) != T3.K2["one"]
        print(f"{kind},p={p},{tag}: e1={T.e1} h1={T.h1} l1={T.l1} l1p={T.l1p}"
              f" g=({T.g0},{T.g1},{T3.g2}) gamma2={T.gamma2} theta2={theta2}"
              f" |K2|={T3.K2['q']} ord(z2)={oz} degPhi3={T3.degPhi3}"
              f" VISIBLE={vis}")
