#!/usr/bin/env python3
"""rm2_postrun_separation.py — POST-RUN SEPARATION ANALYSIS for rm2_probe
(ADDITIVE, display-only; NOT part of the seal; the iterlawr S6 precedent).
Characterizes the MEASURED DCX3 locus on the track-eligible class: which
finer data (s1, u1 residues) separate live from dead rows inside a fixed
(s2,s2') class — the (RM-2)-internal structure S4.7 priced as open."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from grb_order2_check import (pnorm, pmul, ppow, pscal, pdivmod, eq12)
import strata3_probe as S3MOD
import iterlawr_probe as ILP
from iterlaw4_probe import Tower4, Composite4
from rm2_probe import Engine2, ROSTER, anchor2

for tag in ("RM2A", "RM2B", "RM2G"):
    row = [r for r in ROSTER if r[0] == tag][0]
    _, d0, r0, r1, r2, r3, _ = row
    T4 = Tower4("Zp", 3, d0, r0, r1, r2, r3, f"Zp,p3,{tag}")
    E = Engine2(T4); C = Composite4(T4, with_shadow=False)
    T3 = T4.T3; T = T3.T; R = T.R
    e2 = T3.e2; s2g3 = E.s2(T3.gamma3)
    W1 = list(range(C.Gamma0, C.Gamma0 + T4.E4))
    cache = {}
    print(f"\n== {tag} (Zp,3): e1={T.e1}, e2={e2}, s2(gamma3)={s2g3}, "
          f"gamma3={T3.gamma3} ==")
    print("  track-eligible rows (s3=s3'=e2-1, E1IH!=0), grouped by (s2,s2'):")
    rows = {}
    for ga in W1:
        for gb in W1:
            sa = C.split(ga); sb = C.split(gb)
            if not (sa[1] == e2-1 and sb[1] == e2-1): continue
            ah, _ = anchor2(C, cache, ga); bh, _ = anchor2(C, cache, gb)
            E1IH, E0IH = pdivmod(R, pmul(R, ah, bh), T.Phi2)
            if not pnorm(R, E1IH): continue
            Q1, _ = pdivmod(R, pmul(R, E1IH, E.Chat2), T.Phi2)
            live = bool(pnorm(R, Q1))
            key = (sa[2], sb[2])
            rows.setdefault(key, []).append(
                (ga, gb, sa[3], sb[3], sa[7], sb[7], live))
    for key in sorted(rows):
        rs = rows[key]
        nl = sum(1 for r in rs if r[6])
        print(f"   s2-class {key}: {nl}/{len(rs)} live "
              f"(T2+s2g3={key[0]+key[1]+s2g3} vs 2e1={2*T.e1})")
        if 0 < nl < len(rs):
            for (ga, gb, s1a, s1b, u1a, u1b, live) in rs:
                print(f"      ({ga},{gb}) s1=({s1a},{s1b}) "
                      f"u1=({u1a},{u1b}) S1+s(g2)={s1a+s1b+eq12(T.gamma2,T.e0,T.h0)[0]} "
                      f"2e0={2*T.e0} -> {'LIVE' if live else 'dead'}")

# ---- the fitted two-level pattern, checked on EVERY track-eligible row ----
print("\n== FITTED PATTERN CHECK (display-only): DCX3 = TRACK and "
      "[T2+s2(g3) >= 2e1  OR  (= 2e1-1 AND s1+s1'+s1(u0) >= e0)] ==")
bad = 0; tot = 0
for tag in ("RM2A", "RM2B", "RM2G"):
    row = [r for r in ROSTER if r[0] == tag][0]
    _, d0, r0, r1, r2, r3, _ = row
    T4 = Tower4("Zp", 3, d0, r0, r1, r2, r3, f"Zp,p3,{tag}")
    E = Engine2(T4); C = Composite4(T4, with_shadow=False)
    T3 = T4.T3; T = T3.T; R = T.R
    e2 = T3.e2; s2g3 = E.s2(T3.gamma3)
    u0 = (T3.gamma3 - s2g3*T.gamma2)//T.e1      # Chat2 digit's level-1 weight
    s1u0 = eq12(u0, T.e0, T.h0)[0]
    W1 = list(range(C.Gamma0, C.Gamma0 + T4.E4))
    cache = {}
    for ga in W1:
        for gb in W1:
            sa = C.split(ga); sb = C.split(gb)
            if not (sa[1] == e2-1 and sb[1] == e2-1): continue
            ah, _ = anchor2(C, cache, ga); bh, _ = anchor2(C, cache, gb)
            E1IH, _ = pdivmod(R, pmul(R, ah, bh), T.Phi2)
            if not pnorm(R, E1IH): continue
            Q1, _ = pdivmod(R, pmul(R, E1IH, E.Chat2), T.Phi2)
            live = bool(pnorm(R, Q1))
            lvl2 = sa[2] + sb[2] + s2g3
            fit = (lvl2 >= 2*T.e1) or (lvl2 == 2*T.e1 - 1
                                       and sa[3] + sb[3] + s1u0 >= T.e0)
            tot += 1
            if fit != live:
                bad += 1
                print(f"   MISFIT {tag} ({ga},{gb}): live={live} fit={fit}")
    print(f"  {tag}: s1(u0)={s1u0} (u0={u0}); running misfits={bad}")
print(f"FITTED-PATTERN RESULT: {tot-bad}/{tot} rows exact, {bad} misfits")
