#!/usr/bin/env python3
"""POST-SEAL DIAGNOSTIC (labeled; NOT a prereg, NOT a proof step, NOT part of
any seal) for ITERLAW3_PROOF_2026-08-08.md: cross-checks the note's NEW
intermediate claims -- the S4.4/S4.5/S4.6 case partition (CASE-SPLIT), the
Phi2-development digit slots of the anchor product P, the E0-digit identities
w2(E0) = B2 and R2v(E0) = z2^{d2} z1^{d1} eps1(B1), and the full W-MULT-(3)
value -- against the harness of record, on towers exercising every proved
case (II-1 at g0 >= 2, II-1 at g0 = 1, II-2, II-3, e1 = 1) plus the DCX
corner (classified only; the note makes no proof claim there, identities are
still checked as instance evidence). Exact arithmetic; deterministic."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from grb_order2_check import eq12, pmul, ppow, pscal, pnorm, dev
from strata3_probe import Tower3
from iterlawr_probe import Composite3

ROWS = [  # (tag, d0, r0, r1, r2) -- all g1 = 1 so Case II is live
    ("DGA", 1, (2, 1, 2), (2, 1, 1), (2, 1, 1)),   # g0=2: II-1 g0>=2 engine
    ("DGB", 1, (3, 2, 1), (2, 1, 1), (2, 1, 1)),   # row-B shape: DCX live
    ("DGC", 1, (2, 1, 1), (3, 1, 1), (2, 1, 2)),   # e1=3: II-1 g0=1, II-2, II-3
    ("DGD", 1, (3, 2, 1), (1, 1, 1), (2, 1, 1)),   # e1=1: II-3/DCX at e1=1
    ("DGE", 1, (2, 1, 2), (3, 2, 1), (3, 1, 1)),   # g0=2, e1=3, h-track
]
RINGS = [("Zp", 3), ("Fp[[t]]", 2)]

def classify(C, ga, gb):
    T3 = C.T3; T = T3.T
    s3a, s2a, s1a, b2a, b1a, _ = C.split(ga)
    s3b, s2b, s1b, b2b, b1b, _ = C.split(gb)
    S3, S2, S1 = s3a + s3b, s2a + s2b, s1a + s1b
    d1 = S1 // T.e0
    innerII = (T.g0 == 1 and d1 == 1)
    if T.g1 >= 2:
        return "I"
    top = S2 + 1 if innerII else S2
    if top <= T.e1 - 1:
        return "I"
    if not innerII:
        return "II-1"
    sg = eq12(T.gamma2, T.e0, T.h0)[0]
    omega_ge = (S1 - T.e0 + sg >= T.e0)
    if s2a == s2b == T.e1 - 1 and omega_ge:
        return "DCX"
    return "II-2" if S2 >= T.e1 else "II-3"

def run(tag, kind, p, d0, r0, r1, r2):
    T3 = Tower3(kind, p, d0, r0, r1, r2, f"diag/{kind},p={p},{tag}")
    C = Composite3(T3)
    T = T3.T; K2 = T3.K2; K3 = C.K3
    E3 = T3.E3; G0 = C.Gamma0
    counts = {}; bad = []
    for ga in range(G0, G0 + E3):
        for gb in range(G0, G0 + E3):
            cl = classify(C, ga, gb)
            counts[cl] = counts.get(cl, 0) + 1
            s3a, s2a, s1a, b2a, b1a, _ = C.split(ga)
            s3b, s2b, s1b, b2b, b1b, _ = C.split(gb)
            S3 = s3a + s3b; B2 = b2a + b2b; B1 = b1a + b1b
            d3 = S3 // T3.e2
            d2 = (s2a + s2b) // T.e1
            d1 = (s1a + s1b) // T.e0
            P = pmul(T.R, C.anchor(ga), C.anchor(gb))
            d2dev = dev(T.R, P, T.Phi2)
            slots = [j for j, A in enumerate(d2dev) if A]
            # note claim (all proved cases): slots subset of {S3, S3+1},
            # S3 always present
            if cl == "I":
                ok_slots = (slots == [S3])
            else:
                ok_slots = (S3 in slots) and all(j in (S3, S3 + 1)
                                                 for j in slots)
            E0 = d2dev[S3]
            wE0 = T.w2(E0)
            # R2v(E0) target: z2^d2 * z1^d1 * eps1(B1) in K2
            tgt2 = K2["mul"](K2["pow"](T3.z2, d2),
                   K2["mul"](K2["pow"](K2["embed"](T.z1), d1),
                             K2["embed"](T.eps1(B1))))
            r2v = T3.R2v(E0)
            # full W-MULT-(3) value in K3
            tgt3 = K3["mul"](K3["pow"](C.zbar, d3),
                   K3["mul"](K3["embed"](T3.eps2(B2)), K3["embed"](tgt2)))
            v3 = C.val3(P)
            ok = (ok_slots and wE0 == B2 and r2v == tgt2 and v3 == tgt3)
            if not ok:
                bad.append((cl, ga, gb, ok_slots, wE0, B2))
    return counts, bad

def main():
    total_bad = 0; agg = {}
    for kind, p in RINGS:
        for tag, d0, r0, r1, r2 in ROWS:
            counts, bad = run(tag, kind, p, d0, r0, r1, r2)
            total_bad += len(bad)
            for k, v in counts.items():
                agg[k] = agg.get(k, 0) + v
            print(f"{kind},p={p},{tag}: cases {sorted(counts.items())} "
                  f"bad={len(bad)}")
            for b in bad[:5]:
                print("   BAD:", b)
    print("AGGREGATE case census:", sorted(agg.items()))
    print("TOTAL identity violations:", total_bad)
    print("DIAG VERDICT:", "GREEN" if total_bad == 0 else "RED")

if __name__ == "__main__":
    main()
