#!/usr/bin/env python3
"""rmengine_pe2_ext.py — RMENGINE-PE2 (round-2 hostile pass) EXTENSION of PE1's
from-note referee rmengine_pe_reimpl.py (imported READ-ONLY, never mutated).

Object: RMENGINE_2026-08-08.md @ 8835d20 (round-1 repaired text).
Charge slice: the R2 EXTENSION — Lemma L-MU branch (b) (the near-ceiling
induction at d0 = 1) and THEOREM RM-GEN on the d0 = 1 FLAT corners, tested
BEYOND the D7 roster (deeper flats, mixed flat positions, e0 = 1 towers,
g0 = 2 + flat, h0 > 1 + flat, both residue characteristics).

Legs:
  XA  d0 = 1 FLAT towers, STRICT verdict: the four box clauses, tree ==
      canonical division, STRICT mu-descent under the note's BRANCH-(b)
      weights (w_i := midpoint of (S_i, w_{i-1}P_{i-1}), invariant w_i > S_i),
      exact line quanta, the zh kernel, LAW census.  Roster disjoint from
      D7 (FLT-TOP/MID/DBL @ Zp3 + FLT-TOP @ F2t) and PE1's M2C/M3C.
  XB  pure-arithmetic L-MU sweep: (i) branch-(b) note rule strict-satisfies
      the FULL (A_i)/(B_i) system on EVERY d0 = 1 shape (any e_i >= 1),
      m <= 5; (ii) necessity cascade corroboration: d0 >= 2 with a flat
      level 1..m-1 is grid-INFEASIBLE (m <= 4); (iii) branch-(a) note rule
      works whenever all e_i >= 2 (i >= 1), any d0, any e0.

Exit 0 iff zero violations (M.VIOL empty at end).
"""
import sys, os, time
from itertools import product as iproduct
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rmengine_pe_reimpl as M   # PE1's referee, imported read-only

def t_scope_r1(m, d0, es):
    """the AMENDED T-scope (note @8835d20, headline + S4.2 + S5.2):
    d0 = 1  OR  (e0 >= 2 AND e_i >= 2 for all 1 <= i <= m-1)."""
    return d0 == 1 or (es[0] >= 2 and all(es[i] >= 2 for i in range(1, m)))

def branch_b_weights(P, es, tag):
    """The note's S4.1 BRANCH (b) rule verbatim: d0 = 1, rho_0 = P0 - 1,
    rho_l = P_l - 1; w_0 = 1; w_i := midpoint of (S_i, w_{i-1}P_{i-1});
    verify nonemptiness, the invariant w_i > S_i, and (A_i)/(B_i) STRICT."""
    m = len(P)
    rho = [Fraction(P[0] - 1)] + [Fraction(P[l] - 1) for l in range(1, m)]
    w = [Fraction(1)]
    for i in range(1, m):
        S = sum(w[l]*rho[l] for l in range(i))
        hi = w[i-1]*P[i-1]
        if not S < hi:
            M.viol("X-IVL", tag, f"branch-(b) interval EMPTY at i={i}: ({S},{hi})")
            return None
        w.append((S + hi)/2)
    for i in range(1, m):
        S = sum(w[l]*rho[l] for l in range(i))
        if not w[i] > S:
            M.viol("X-IVL", tag, f"branch-(b) invariant w_{i} > S_{i} FAILS")
        if not w[i] < w[i-1]*P[i-1]:
            M.viol("X-IVL", tag, f"(A_{i}) FAILS for branch-(b) weights")
        if not w[i]*es[i] > S:
            M.viol("X-IVL", tag, f"(B_{i}) FAILS for branch-(b) weights")
    return w

# ---------------- XA: the flat-tower roster (all d0 = 1, amended-scope) ------
XROSTER = [
    # tag,  m, kind,  p, d0, reads  — every shape has a flat level in 1..m-1
    # or an e0 = 1 degeneracy; NONE coincides (shape, ring) with D7 or M2C/M3C.
    ("X1-e0flat",   2, "Zp",  5, 1, [(1,1,1), (1,1,1), (2,1,1)]),  # e0=1 + e1=1
    ("X2-g02flat",  2, "Zp",  3, 1, [(2,1,2), (1,1,1), (2,1,1)]),  # g0=2, flat e1
    ("X3-h02flat",  2, "Zp",  5, 1, [(3,2,1), (1,1,1), (2,1,1)]),  # e0=3 h0=2, flat e1
    ("X4-dbl-p5",   3, "Zp",  5, 1, [(2,1,1), (1,1,1), (1,1,1), (2,1,1)]),  # double flat @Zp5
    ("X5-mid-F2t",  3, "Fpt", 2, 1, [(2,1,1), (1,1,1), (2,1,1), (2,1,1)]),  # flat-mid cross-ring
    ("X6-m4mid",    4, "Zp",  3, 1, [(2,1,1), (2,1,1), (1,1,1), (2,1,1), (2,1,1)]),  # m=4 mid-flat
    ("X7-m4mix",    4, "Zp",  3, 1, [(2,1,1), (1,1,1), (2,1,1), (1,1,1), (2,1,1)]),  # m=4 flats @1,3
    ("X8-e0mix",    3, "Zp",  3, 1, [(1,1,1), (2,1,1), (1,1,1), (2,1,1)]),  # e0=1, flat e2
]

def leg_XA():
    print("== XA: d0=1 FLAT towers, STRICT verdict, branch-(b) weights ==")
    mut = dict(MU1=0, MU2=0, MU3=0, MU4=0, MU5=0, MU6=0, MU7=0)
    total_calls0 = M.CNT.get("engine_calls", 0)
    for (tag, m, kind, p, d0, reads) in XROSTER:
        es = [r[0] for r in reads]
        if not t_scope_r1(m, d0, es[:m]):
            M.viol("X-SCOPE", tag, "roster shape off the AMENDED T-scope")
        old = M.t_scope(m, d0, es[:m])
        print(f"-- {tag}: m={m} {kind} p={p} d0={d0} reads={reads} "
              f"(old T-scope0: {old} -> NEW at r1: {not old})")
        E = M.Eng(m, kind, p, d0, reads, tag)
        M.prep(E)
        w = branch_b_weights(E.P, E.e, tag)
        if w is None:
            continue
        stats = M.new_stats(m)
        nin = 0
        for (nm, f) in M.battery(E):
            M.engine_run(E, f, w, True, stats, mut)   # strict=True: mu VERDICT
            nin += 1
        law = M.law_leg(E, mut)
        print(f"   calls={nin} nodes={stats['nodes']} promo={stats['promo']} "
              f"exit={stats['exit']} corrL={stats['corrL']} "
              f"junk={stats['junkX']}/{stats['junkY']} maxj={stats['maxj']} "
              f"mu_non_descending={stats['mu_flat_up']}")
        print(f"   branch-(b) weights={[str(x) for x in w]}")
        if law:
            print(f"   LAW-DCX-{m+1}: pairs={law['pairs']} live={law['live']} "
                  f"chainfed={law['chainfed']} mism={law['mism']}")
    calls = M.CNT.get("engine_calls", 0) - total_calls0
    print(f"XA total fresh flat-tower engine calls: {calls}; "
          f"v=0 realized: {M.CNT.get('v_zero_inputs', 0)}")
    return calls

# ---------------- XB: pure-arithmetic L-MU sweep ------------------------------
def leg_XB():
    print("== XB: L-MU arithmetic sweep (branch (b) / necessity / branch (a)) ==")
    nb = nb_bad = 0
    gsets = lambda m: [(1,)*m, (2,) + (1,)*(m-1), (2,)*m]
    # (i) branch (b) on EVERY d0=1 shape, m <= 5, e_i in {1,2,3}
    for m in range(2, 6):
        for es in iproduct((1, 2, 3), repeat=m):
            for gs in gsets(m):
                P = [es[l]*gs[l] for l in range(m)]
                nb += 1
                before = len(M.VIOL)
                wv = branch_b_weights(P, list(es), f"XB-b-{es}-{gs}")
                if wv is None or len(M.VIOL) > before:
                    nb_bad += 1
    print(f"   (i) branch-(b) rule on d0=1 shapes: {nb} shapes, "
          f"{nb_bad} failures (predicted 0)")
    # (ii) d0 >= 2 with a flat level 1..m-1: full system grid-INFEASIBLE
    ni = ni_bad = 0
    for m in range(2, 5):
        for es in iproduct((1, 2, 3), repeat=m):
            if not any(es[i] == 1 for i in range(1, m)):
                continue
            for gs in gsets(m):
                ni += 1
                r = M.ab_probe(2, [(es[l], gs[l]) for l in range(m)])
                if r["grid"]:
                    ni_bad += 1
                    M.viol("X-NEC", f"XB-nec-{es}-{gs}",
                           f"d0=2 flat shape FEASIBLE: witness {r['witness']}")
    print(f"   (ii) necessity cascade: {ni} d0>=2 flat shapes probed, "
          f"{ni_bad} feasible (predicted 0)")
    # (iii) branch (a): all e_i >= 2 (i >= 1), any e0, any d0 — note rule works
    na = na_bad = 0
    for m in range(2, 5):
        for es in iproduct((1, 2, 3), repeat=m):
            if any(es[i] == 1 for i in range(1, m)):
                continue
            for d0 in (1, 2):
                for gs in gsets(m):
                    na += 1
                    r = M.ab_probe(d0, [(es[l], gs[l]) for l in range(m)])
                    if not r["noterule"]:
                        na_bad += 1
                        M.viol("X-BRA", f"XB-a-{es}-{gs}-d{d0}",
                               "branch-(a) midpoint rule FAILED on its scope")
    print(f"   (iii) branch-(a) rule on its scope: {na} shapes, "
          f"{na_bad} failures (predicted 0)")

def main():
    t0 = time.time()
    calls = leg_XA()
    leg_XB()
    xviol = [v for v in M.VIOL]
    print()
    fams = {}
    for (f, t, d) in xviol:
        fams[f] = fams.get(f, 0) + 1
    for fam, lab in [("V-BOX", "four box clauses (flat towers)"),
                     ("V-MU", "STRICT mu-descent under branch-(b) weights"),
                     ("V-CONS", "tree == canonical division"),
                     ("V-LINE", "line calculus exact quanta"),
                     ("V-ZH", "zh kernel / B-READ / L-ZMULT"),
                     ("V-ID", "identity exactness + Chat certificates"),
                     ("X-IVL", "branch-(b) intervals + (A)/(B) strict"),
                     ("X-SCOPE", "amended-scope predicate"),
                     ("X-NEC", "necessity cascade (d0>=2 flat infeasible)"),
                     ("X-BRA", "branch-(a) rule on its scope"),
                     ("V-LAW", "LAW structure (u-chain, L-CAP)"),
                     ("V-P0", "harness eps tie")]:
        n = fams.get(fam, 0)
        print(f"XV {fam:8s} ({lab}): "
              f"{'GREEN [0 violations]' if n == 0 else f'RED [{n} violations]'}")
    ok = len(xviol) == 0
    print(f"\nPE2-EXT TOTAL: {'ALL GREEN' if ok else str(len(xviol)) + ' VIOLATIONS'}"
          f"; census notes: {len(M.CENS)}; engine calls (flat, fresh): {calls}; "
          f"elapsed {time.time()-t0:.1f}s")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
