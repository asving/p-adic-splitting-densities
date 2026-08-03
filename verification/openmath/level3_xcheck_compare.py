#!/usr/bin/env python3
# level3_xcheck_compare.py -- M5 step 4: MATCHED-INSTANCE raw-value comparison
# (POST-SEAL DIAGNOSTIC; NOT PREREGISTERED).  Run AFTER level3_xcheck.py's own
# F0 + measurement phases (decorrelation honored: the sealed runner was first
# opened only for this step).
#
# Compares, on the sealed roster's d0=1 rows (H excluded: this control is d0=1-only),
# over all four rings, per pair (gamma,gamma') in the sealed W1xW1 block:
#   LEG-P (plain lift):        my tower with THEIR psi's, MY plain pattern Phi2
#                              vs their Composite3 cocycle (lift-convention robustness);
#   LEG-T (transplanted lift): my tower with THEIR Phi0/Phi1/Phi2 transplanted verbatim
#                              (so ONLY the read calculus differs) vs their cocycle;
#   LEG-A (anchor values):     my val3(phi_gamma) vs their anchor_val, W1 letters,
#                              transplanted towers.
# Field elements are compared exactly (their K0 = d0-tuples of ints; mine = ints;
# structural conversion wraps/unwraps the base coordinate).

import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import level3_xcheck as MX
import iterlawr_probe as ILP
from iterlawr_probe import Composite3
from strata3_probe import Tower3

def convT2M(level, x):
    # their K_level element -> mine (d0 = 1)
    if level == 0: return x[0]
    return tuple(convT2M(level - 1, c) for c in x)

def convM2T(level, x):
    # my K_level element -> theirs (d0 = 1)
    if level == 0: return (x,)
    return tuple(convM2T(level - 1, c) for c in x)

def conv_psi(level, psi):
    # their monic psi (list len g+1 of K_level elems) -> my modulus [c0..c_{g-1}]
    return [convT2M(level, c) for c in psi[:-1]]

def main():
    lines = []
    def log(s):
        print(s); lines.append(s)
    log("level3_xcheck_compare.py -- matched-instance cross-implementation comparison")
    tot = dict(P=0, T=0, A=0); bad = dict(P=0, T=0, A=0)
    phi1_same = 0; phi1_diff = 0; phi2_same = 0; phi2_diff = 0
    first_div = None
    for kind, p in ILP.CONFIGS:
        for tag, d0, r0, r1, r2 in ILP.ROWS:
            if d0 != 1: continue
            full = f"{kind},p={p},{tag}"
            T3 = Tower3(kind, p, d0, r0, r1, r2, full)
            C = Composite3(T3)
            E3 = T3.E3
            W1 = list(range(C.Gamma0, C.Gamma0 + E3))
            # my tower with THEIR psi's
            R = MX.ZRing(p) if kind == "Zp" else MX.TRing(p)
            psi0m = conv_psi(0, T3.T.psi0)
            psi1m = conv_psi(1, T3.T.psi1)
            psi2m = conv_psi(2, T3.psi2)
            reads = [(r0[0], r0[1], psi0m), (r1[0], r1[1], psi1m),
                     (r2[0], r2[1], psi2m)]
            Tp = MX.Tower(R, reads)          # LEG-P: my plain Phi2
            # construction diffs (informational)
            if Tp.Phi[1] == list(T3.T.Phi1): phi1_same += 1
            else: phi1_diff += 1
            if Tp.Phi[2] == list(T3.T.Phi2): phi2_same += 1
            else: phi2_diff += 1
            # integer frame must agree
            assert Tp.gammaW[2] == T3.T.gamma2 and Tp.gammaW[3] == T3.gamma3
            assert Tp.wPhi[1] == T3.T.w1Phi1 and Tp.wPhi[2] == T3.T.w2Phi2
            # LEG-T tower: transplant their Phi chain verbatim
            Tt = MX.Tower(R, reads)
            Tt.Phi[0] = list(T3.T.Phi0); Tt.Phi[1] = list(T3.T.Phi1)
            Tt.Phi[2] = list(T3.T.Phi2); Tt._phipowcache = {}
            assert len(Tt.Phi[2]) - 1 == len(Tp.Phi[2]) - 1
            nP = nT = nA = 0
            for g in W1:
                tot['A'] += 1
                poly, diag = Tt.anchor(g)
                wv, vm = Tt.valN(poly)
                if convM2T(3, vm) != C.anchor_val(g):
                    bad['A'] += 1; nA += 1
                    if first_div is None:
                        first_div = ("LEG-A", full, g, None, vm, C.anchor_val(g))
            for ga in W1:
                for gb in W1:
                    ct = C.cocycle(ga, gb)[0]
                    tot['P'] += 1
                    cp, _ = Tp.cocycle(ga, gb)
                    if cp is None or convM2T(3, cp) != ct:
                        bad['P'] += 1; nP += 1
                        if first_div is None:
                            first_div = ("LEG-P", full, ga, gb, cp, ct)
                    tot['T'] += 1
                    cm, _ = Tt.cocycle(ga, gb)
                    if cm is None or convM2T(3, cm) != ct:
                        bad['T'] += 1; nT += 1
                        if first_div is None:
                            first_div = ("LEG-T", full, ga, gb, cm, ct)
            log(f"{full:16} E3={E3:>2} W1=[{W1[0]}..{W1[-1]}] "
                f"Phi1{'==' if Tp.Phi[1] == list(T3.T.Phi1) else '!='} "
                f"Phi2{'==' if Tp.Phi[2] == list(T3.T.Phi2) else '!='} | "
                f"divergences: plain={nP} transplant={nT} anchors={nA}")
    log("")
    log(f"Phi1 construction identical: {phi1_same}/{phi1_same+phi1_diff} towers; "
        f"Phi2 identical (plain vs their corrected): {phi2_same}/{phi2_same+phi2_diff}")
    log(f"LEG-A anchors : {tot['A']} matched, {bad['A']} divergent")
    log(f"LEG-P plain   : {tot['P']} matched pairs, {bad['P']} divergent")
    log(f"LEG-T transplant: {tot['T']} matched pairs, {bad['T']} divergent")
    if first_div: log(f"FIRST DIVERGING TUPLE: {first_div}")
    verdict = ("HARNESS-CONFIRMED (both implementations measure the same cocycle)"
               if bad['T'] == 0 and bad['A'] == 0 else "HARNESS-DIVERGENT")
    log(f"VERDICT: {verdict}")
    with open("level3_xcheck_compare_output.txt", "w") as f:
        f.write("\n".join(lines) + "\n")
    return 0 if bad['T'] == 0 and bad['A'] == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
