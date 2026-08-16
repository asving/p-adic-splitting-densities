#!/usr/bin/env python3
"""
A-C.5 certification: the SWEEP layer of the C.109 SPLIT (blueprint
CHAP-C_tower_grammar.md, NODE C.109-v `ht_sweep_census`, amendment A-C.5,
2026-08-16).  Companion to `c109_ac2_cell_check.py`, whose FQ arithmetic,
polygon encodings and cell counter are imported rather than re-derived.

WHAT IS CHECKED

  [SWEEP]  NODE C.109-v, exactly as signed: for a well-formed node `v`, the
           number of PRICED-DIGIT ASSIGNMENTS

             r : N -> F_Q   with   r j = 0 off the on-hull positions j < m,
                                   r m = 1                (monic top),
                                   r j != 0 at every VERTEX j <= m,
                                   residualTypeOf(R_S(r)) = lambda_S for
                                     every side S of the node polygon,
             R_S(r) := sum_k r(min(sideSet_S) + l*k) Y^k,  k <= sideDeg_S,

           equals  prod_S sideCensus(lambda_S)  --  EFF.W12.24's right-to-left
           sweep, "no extra unit factors".  Instances: the A-C.2 shared-vertex
           polygon I6 (Pceil = (3,1,0): two degree-1 sides sharing the vertex
           j = 1) and the NEW instance I7 (Pceil = (5,2,1,0): a degree-1 side
           and a degree-2 side sharing the vertex j = 1, with an INTERIOR
           lattice point at j = 2 -- the shape where the shared unit is spent
           by a census of degree > 1), at q = 2 and q = 3, every quadratic
           type; plus I8 (Pceil = (7,3,1,0,0)): FOUR degree-1 sides, three
           interior shared vertices -- the maximal-exposure instance for the
           archived draft's spurious per-vertex unit factor; plus I3
           (Pceil = (1,1,0)): a position BELOW the top that is NOT on the hull.

  [XCELL]  Consistency of the sweep layer with the FULL cell law (C.109's
           assembly): the measured cell count divided by Q^{B_v(N)} equals the
           measured assignment count.  Run at I6 (q = 2, 3) and at the NEW I7
           (q = 2, N = 6 -- window-visibility needs N > 5).

  [DICT]   NODE C.109-iv's shape, certified BEFORE it is signed: the naive
           dictionary `sideSet(f) = nodeSideSet(v)` is FALSE on the re-signed
           cell -- a priced digit at a NON-VERTEX on-side lattice point may
           VANISH, and then that abscissa is not attaining.  Exhibited at
           I2/q=2 with the double-root type.  What survives, and is what the
           node signs, is: containment, equality of the two ENDPOINTS, equality
           of the residual degree, and the left-endpoint height = Pceil.

  [MUT]    Four mutations, each must KILL the sweep law:
           T-SWEEP-UNIT    the archived draft's error: one extra (Q-1) factor
                           per INTERIOR shared vertex.  BLIND at q = 2 (Q-1=1)
                           and recorded as such -- the reason the law is
                           certified at two primes.
           T-SWEEP-VERTEX  drop the vertex-nonvanishing clause (the type
                           conditions alone do NOT imply it: a residual may
                           have a zero constant term and still have type
                           lambda whenever lambda contains a linear factor).
           T-SWEEP-TOP     drop the monic top `r m = 1` (allow any unit); also
                           blind at q = 2, recorded.
           T-SWEEP-HULL    price the positions that are NOT on the hull (they
                           belong to the Q^B digit count, not to the census).

Exit 0 iff every check passes.  Run:  python3 c109_ac5_sweep_check.py
"""

import itertools, sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from c109_ac2_cell_check import (
    FQ, poly_trim, factor_type, monic_normalize, side_census,
    lean_OnHull, lean_IsVertex, lean_nodeSideSet, lean_IsSide, lean_nodeSideDeg,
    lean_WF_data, direct_polygon_data, dev, gauss_val, side_reads, lhs_count,
)

FAIL = 0
CHECKS = 0


def check(name, cond, detail=""):
    global FAIL, CHECKS
    CHECKS += 1
    tag = "PASS" if cond else "FAIL"
    if not cond:
        FAIL += 1
    print(f"[{tag}] {name}" + (f"  ({detail})" if detail else ""))


# ---------------------------------------------------------------------------
# The signed assignment set of NODE C.109-v, transcribed clause by clause
# ---------------------------------------------------------------------------

def sweep_count(F, P, m, types, *, drop_vertex=False, free_top=False,
                price_offhull=False):
    """#{r : the C.109-v assignment set}.  The keyword arguments are the
    mutations; with all of them False this is the signed statement."""
    onhull = [j for j in range(m) if lean_OnHull(P, m, j)]
    priced = list(onhull)
    if price_offhull:
        priced = list(range(m))
    verts = [j for j in range(m + 1) if lean_IsVertex(P, m, j)]
    tops = F.elems if free_top else [F.one]
    if free_top:
        tops = [x for x in F.elems if x != F.zero]
    cnt = 0
    for vals in itertools.product(F.elems, repeat=len(priced)):
        for top in tops:
            r = {j: F.zero for j in range(m + 1)}
            for j, x in zip(priced, vals):
                r[j] = x
            r[m] = top
            if not drop_vertex and any(r[j] == F.zero for j in verts):
                continue
            ok = True
            for (u, l), lam in types.items():
                ss = lean_nodeSideSet(P, m, u, l)
                j0, g = min(ss), lean_nodeSideDeg(P, m, u, l)
                res = poly_trim(F, [r.get(j0 + l * k, F.zero) for k in range(g + 1)])
                if len(res) <= 1:
                    ok = False
                    break
                if factor_type(F, monic_normalize(F, res)) != lam:
                    ok = False
                    break
            if ok:
                cnt += 1
    return cnt


def census_product(F, types):
    val = 1
    for lam in types.values():
        val *= side_census(F, lam)
    return val


def node_of(P, m, types, label):
    """Build + WF-check a node, and assert the types are given for exactly the
    genuine sides (the WF clause (iv)/(v) pairing)."""
    okc, L, lean_sides = lean_WF_data(P, m)
    H, onhull, verts, dsides = direct_polygon_data(P, m)
    check(f"WF ceiled-consistency {label}", okc)
    check(f"WF sides = the genuine sides {label}", set(lean_sides) == set(types),
          f"lean={sorted(lean_sides)} typed={sorted(types)}")
    check(f"WF/ENC sides agree with the direct hull {label}",
          set(lean_sides) == set(dsides))
    for s, lam in types.items():
        check(f"WF side-type degree law at {s} {label}",
              sum(dd * mm for dd, mm in lam) == lean_sides[s])
    return {"m": m, "Pceil": P, "L": L, "sides": types}


def sweep_law(F, P, m, types, label):
    lhs = sweep_count(F, P, m, types)
    rhs = census_product(F, types)
    check(f"SWEEP {label}", lhs == rhs, f"assignments={lhs} prod_S S_lambda={rhs}")
    return lhs


def interior_vertices(P, m):
    return [j for j in range(1, m) if lean_IsVertex(P, m, j)]


def main():
    print("=" * 78)
    print("A-C.5 certification: NODE C.109-v (the right-to-left sweep + census")
    print("product), with the C.109-iv dictionary shape and four teeth")
    print("=" * 78)

    LIN = ((1, 1),)
    QUADS = (((1, 2),), ((1, 1), (1, 1)), ((2, 1),))

    for p in (2, 3):
        F = FQ(p)

        # ---- I6: the A-C.2 shared-vertex instance -------------------------
        P6, m6 = [3, 1, 0], 2
        t6 = {(2, 1): LIN, (1, 1): LIN}
        n6 = node_of(P6, m6, t6, f"I6 q={p}")
        check(f"I6 q={p}: L = 2", n6["L"] == 2)
        check(f"I6 q={p}: one INTERIOR shared vertex", interior_vertices(P6, m6) == [1])
        sweep_law(F, P6, m6, t6, f"I6 q={p} (two sides, shared vertex)")

        # ---- I7 (NEW): degree-1 + degree-2 sides sharing a vertex ---------
        P7, m7 = [5, 2, 1, 0], 3
        for lam in QUADS:
            t7 = {(3, 1): LIN, (1, 1): lam}
            n7 = node_of(P7, m7, t7, f"I7 q={p} lam={lam}")
            check(f"I7 q={p}: L = 3 (j = 0,1,2 on hull)", n7["L"] == 3)
            check(f"I7 q={p}: j = 2 is on the hull but NOT a vertex",
                  lean_OnHull(P7, m7, 2) and not lean_IsVertex(P7, m7, 2))
            check(f"I7 q={p}: one INTERIOR shared vertex (j = 1)",
                  interior_vertices(P7, m7) == [1])
            sweep_law(F, P7, m7, t7, f"I7 q={p} (deg-1 + deg-2, shared vertex, lam={lam})")

        # ---- I8 (NEW): four degree-1 sides, three interior vertices -------
        P8, m8 = [7, 3, 1, 0, 0], 4
        t8 = {(4, 1): LIN, (2, 1): LIN, (1, 1): LIN, (0, 1): LIN}
        n8 = node_of(P8, m8, t8, f"I8 q={p}")
        check(f"I8 q={p}: L = 4", n8["L"] == 4)
        check(f"I8 q={p}: THREE interior shared vertices",
              interior_vertices(P8, m8) == [1, 2, 3])
        sweep_law(F, P8, m8, t8, f"I8 q={p} (four sides, three shared vertices)")

        # ---- I3: a position below the top that is NOT on the hull ---------
        P3, m3 = [1, 1, 0], 2
        t3 = {(1, 2): LIN}
        n3 = node_of(P3, m3, t3, f"I3 q={p}")
        check(f"I3 q={p}: L = 1 (j = 1 is OFF the hull)",
              n3["L"] == 1 and not lean_OnHull(P3, m3, 1))
        sweep_law(F, P3, m3, t3, f"I3 q={p} (ell = 2 side, an off-hull position)")

        # ---------------- MUTATIONS ---------------------------------------
        # T-SWEEP-UNIT: the archived draft's spurious per-interior-vertex unit.
        # BLIND AT q = 2 by construction (Q - 1 = 1), which is exactly why the
        # law is certified at two primes; asserted as an equality there so the
        # blindness is a recorded fact and not a silent skip.
        for (P, m, types, label) in ((P6, m6, t6, "I6"), (P8, m8, t8, "I8")):
            true_cnt = sweep_count(F, P, m, types)
            bad = census_product(F, types) * (F.Q - 1) ** len(interior_vertices(P, m))
            if F.Q == 2:
                check(f"T-SWEEP-UNIT q={p} {label}: mutant is BLIND at Q = 2 (recorded)",
                      bad == true_cnt, f"mutant={bad} true={true_cnt}")
            else:
                check(f"T-SWEEP-UNIT q={p} {label}: the per-vertex unit factor is KILLED",
                      bad != true_cnt, f"mutant={bad} true={true_cnt}")

        # T-SWEEP-VERTEX: drop the vertex clause.  Killed wherever a side type
        # admits a residual with a zero constant term (any lambda with a linear
        # factor) or wherever a left vertex is unconstrained by its side type.
        for (P, m, types, label) in ((P6, m6, t6, "I6"), (P8, m8, t8, "I8")):
            true_cnt = sweep_count(F, P, m, types)
            mut = sweep_count(F, P, m, types, drop_vertex=True)
            check(f"T-SWEEP-VERTEX q={p} {label}: vertex-nonvanishing is LOAD-BEARING",
                  mut != true_cnt, f"mutant={mut} true={true_cnt}")

        # T-SWEEP-TOP: a free unit top instead of the monic 1.  Also blind at
        # q = 2 (the only unit IS 1), recorded the same way.
        for (P, m, types, label) in ((P6, m6, t6, "I6"), (P7, m7, {(3, 1): LIN, (1, 1): ((2, 1),)}, "I7")):
            true_cnt = sweep_count(F, P, m, types)
            mut = sweep_count(F, P, m, types, free_top=True)
            if F.Q == 2:
                check(f"T-SWEEP-TOP q={p} {label}: mutant is BLIND at Q = 2 (recorded)",
                      mut == true_cnt, f"mutant={mut} true={true_cnt}")
            else:
                check(f"T-SWEEP-TOP q={p} {label}: the monic top is LOAD-BEARING",
                      mut != true_cnt, f"mutant={mut} true={true_cnt}")

        # T-SWEEP-HULL: pricing an off-hull position (only I3 has one)
        true_cnt = sweep_count(F, P3, m3, t3)
        mut = sweep_count(F, P3, m3, t3, price_offhull=True)
        check(f"T-SWEEP-HULL q={p} I3: off-hull positions are NOT priced",
              mut != true_cnt, f"mutant={mut} true={true_cnt}")

    # ---------------------------------------------------------------------
    # [XCELL] the sweep layer against the FULL cell law
    # ---------------------------------------------------------------------
    def xcell(F, p, N, P, m, types, label):
        node = {"m": m, "Pceil": P, "L": lean_WF_data(P, m)[1], "sides": types}
        B = m * N - sum(P[j] for j in range(m)) - node["L"]
        lhs = lhs_count(F, p, N, [0, 1], node)
        sw = sweep_count(F, P, m, types)
        check(f"XCELL {label}: cell = Q^B * (sweep count)",
              lhs == F.Q ** B * sw, f"cell={lhs} Q^{B}={F.Q ** B} sweep={sw}")

    for p in (2, 3):
        F = FQ(p)
        xcell(F, p, 5, [3, 1, 0], 2, {(2, 1): ((1, 1),), (1, 1): ((1, 1),)}, f"I6 q={p} N=5")
    xcell(FQ(2), 2, 6, [5, 2, 1, 0], 3,
          {(3, 1): ((1, 1),), (1, 1): ((2, 1),)}, "I7 q=2 N=6 (NEW)")

    # ---------------------------------------------------------------------
    # [DICT] NODE C.109-iv: the naive set equality is FALSE; the endpoints hold
    # ---------------------------------------------------------------------
    p, N = 2, 5
    F = FQ(p)
    P2, m2 = [2, 1, 0], 2
    t2 = {(1, 1): ((1, 2),)}          # the char-2 double root: interior digit 0
    node2 = {"m": m2, "Pceil": P2, "L": lean_WF_data(P2, m2)[1], "sides": t2}
    witness = None
    for a in itertools.product(range(p ** N), repeat=m2):
        f = list(a) + [1]
        devs = dev(p ** N, [0, 1], f, m2)
        nph = [gauss_val(p, N, x) for x in devs]
        # membership in the RE-SIGNED cell, clause by clause
        okmem = True
        for j in range(m2 + 1):
            h = nph[j]
            if not (h is None or h >= P2[j]):
                okmem = False
            if lean_IsVertex(P2, m2, j) and h != P2[j]:
                okmem = False
        if okmem:
            r = side_reads(F, p, N, [0, 1], devs, m2, 1, 1)
            if r is not None:
                ss, j0, H0, res = r
                if len(res) > 1 and factor_type(F, monic_normalize(F, res)) == ((1, 2),):
                    if set(ss) != set(lean_nodeSideSet(P2, m2, 1, 1)):
                        witness = (f, ss, j0, H0)
                        break
    check("DICT: a cell member with sideSet STRICTLY inside nodeSideSet exists "
          "(so C.109-iv must be signed with containment, not equality)",
          witness is not None,
          f"witness f={witness[0] if witness else None} sideSet={witness[1] if witness else None} "
          f"nodeSideSet={lean_nodeSideSet(P2, m2, 1, 1)}")
    if witness is not None:
        f, ss, j0, H0 = witness
        nss = lean_nodeSideSet(P2, m2, 1, 1)
        check("DICT: containment holds at the witness", set(ss) <= set(nss))
        check("DICT: the two ENDPOINTS agree at the witness",
              min(ss) == min(nss) and max(ss) == max(nss))
        check("DICT: the residual degree agrees at the witness",
              (max(ss) - min(ss)) // 1 == lean_nodeSideDeg(P2, m2, 1, 1))
        check("DICT: the left-endpoint height is Pceil at the witness",
              H0 == P2[j0])

    print("=" * 78)
    print(f"CHECKS: {CHECKS}, FAILURES: {FAIL}")
    if FAIL:
        print("RESULT: FAILURES")
        return 1
    print("RESULT: ALL CHECKS PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
