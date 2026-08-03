#!/usr/bin/env python3
"""iterlawr_separation_analysis.py — POST-HOC ANALYSIS, NOT PREREGISTERED.

Post-run companion to the sealed ITER-LAW-r probe (seal 911431c; outputs
iterlawr_probe_results.json).  The sealed PRIMARY candidate passed every
preregistered leg (0 violations / 103,772 samples); the only failing form in
the whole battery is the DISTINGUISHED NAIVE ALTERNATIVE (per-level template,
prereg S1), which fails on 1752 / 13440 pairs.  This script extracts the
small-case evidence of that separation:

  PASS 1 (aggregate, all 52 towers, W1xW1): classify every naive-diff pair
     as NONINTEGRAL (naive inner exponent D1n not an integer) or FIELD-DIFF
     (both integral, values differ); check the localization claims:
       (L1) every separation pair has d3 = 1 (top carry live);
       (L2) every FIELD-DIFF discrepancy factor measured/naive equals
            z1^(D1 - D1n) exactly (pure z1-power; no zbar/z2 leakage).
  PASS 2 (detail, smallest-E3 rows first): full tuples — (gamma,gamma'),
     splits, constants, measured c3, naive prediction, discrepancy factor.

Consumes the sealed module read-only; no verdicts here, display only.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iterlawr_probe as IP
from strata3_probe import Tower3

def sep_scan(C, T3, W):
    """yield (ga, gb, cst, kind, meas, nv) for naive!=primary pairs."""
    for ga in W:
        for gb in W:
            cst = C.constants(ga, gb)
            lawv = C.law_value(cst, "primary")
            nv = C.law_value(cst, "naive")
            if nv is None:
                yield ga, gb, cst, "NONINTEGRAL", C.cocycle(ga, gb)[0], None
            elif lawv is not None and nv != lawv:
                yield ga, gb, cst, "FIELD-DIFF", C.cocycle(ga, gb)[0], nv

def main():
    # ---------------- PASS 1: aggregate over all 52 towers ----------------
    tot = dict(NONINTEGRAL=0, FIELDDIFF=0)
    bad_l1 = []   # separation pairs with d3 != 1
    bad_l2 = []   # FIELD-DIFF pairs where factor != z1^(D1-D1n)
    for kind, p in IP.CONFIGS:
        for tag, d0, r0, r1, r2 in IP.ROWS:
            full = f"{kind},p={p},{tag}"
            T3 = Tower3(kind, p, d0, r0, r1, r2, full)
            C = IP.Composite3(T3)
            K3 = C.K3
            W1 = list(range(C.Gamma0, C.Gamma0 + T3.E3))
            for ga, gb, cst, k, meas, nv in sep_scan(C, T3, W1):
                tot["NONINTEGRAL" if k == "NONINTEGRAL" else "FIELDDIFF"] += 1
                if cst["d3"] != 1:
                    bad_l1.append((full, ga, gb, cst["d3"]))
                if k == "FIELD-DIFF":
                    fac = K3["mul"](meas, K3["inv"](nv))
                    want = K3["pow"](C.z1_3, cst["D1"] - cst["D1n"])
                    if fac != want:
                        bad_l2.append((full, ga, gb))
    print("PASS 1 (all 52 towers, W1xW1): naive/composed separation census")
    print(f"  NONINTEGRAL (naive D1n not in Z): {tot['NONINTEGRAL']}")
    print(f"  FIELD-DIFF  (integral, values differ): {tot['FIELDDIFF']}")
    print(f"  (L1) all separation pairs have d3 = 1: "
          f"{'CONFIRMED' if not bad_l1 else 'FALSE: ' + str(bad_l1[:5])}")
    print(f"  (L2) every FIELD-DIFF factor == z1^(D1-D1n): "
          f"{'CONFIRMED' if not bad_l2 else 'FALSE: ' + str(bad_l2[:5])}")
    print()
    # ---------------- PASS 2: detailed tuples, smallest rows --------------
    detail = [("Zp", 3, "CW"), ("Zp", 2, "A"), ("Zp", 3, "G"), ("Zp", 3, "C")]
    rowmap = {t: (t, d0, r0, r1, r2) for t, d0, r0, r1, r2 in IP.ROWS}
    for kind, p, tag in detail:
        t, d0, r0, r1, r2 = rowmap[tag]
        full = f"{kind},p={p},{tag}"
        T3 = Tower3(kind, p, d0, r0, r1, r2, full)
        C = IP.Composite3(T3); T = T3.T; K3 = C.K3
        W1 = list(range(C.Gamma0, C.Gamma0 + T3.E3))
        print(f"--- {full}  (e,h,g) = {r0} {r1} {r2}   E3={T3.E3}  "
              f"gamma2={T.gamma2} gamma3={T3.gamma3} "
              f"(l0,l0')=({T.l0},{T.l0p}) (l1,l1')=({T.l1},{T.l1p})")
        shown = 0
        for ga, gb, cst, k, meas, nv in sep_scan(C, T3, W1):
            if shown >= 3:
                break
            shown += 1
            d2 = cst["d2"]
            gam2d2 = T.gamma2*d2
            print(f"  pair ({ga},{gb})  [{k}]  d3={cst['d3']} d2={d2} "
                  f"D2={cst['D2']}  Sig={cst['Sig']} vs naive gamma2*d2="
                  f"{gam2d2}  D1={cst['D1']} vs D1naive={cst['D1n']}")
            print(f"    measured c3 = {IP.k3_repr(C, meas)}")
            if nv is None:
                num = (cst['b1a'] is not None)
                s1a = C.split(ga)[2]; s1b = C.split(gb)[2]
                s1c = C.split(ga+gb)[2]
                print(f"    naive: NO VALUE — e0={T.e0} does not divide "
                      f"s1-defect+l0*gamma2*d2 = "
                      f"{s1a+s1b-s1c}+{T.l0}*{gam2d2} = "
                      f"{s1a+s1b-s1c+T.l0*gam2d2}")
            else:
                fac = K3["mul"](meas, K3["inv"](nv))
                print(f"    naive pred  = {IP.k3_repr(C, nv)}   "
                      f"discrepancy factor measured/naive = "
                      f"{IP.k3_repr(C, fac)} = z1^{cst['D1']-cst['D1n']}")
        if shown == 0:
            print("  (no separation pairs on W1xW1)")
        print()

if __name__ == "__main__":
    main()
