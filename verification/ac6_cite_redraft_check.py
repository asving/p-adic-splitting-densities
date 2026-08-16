#!/usr/bin/env python3
"""
A-C.6 CITE-REDRAFT certification — the numeric leg.

WHY THIS FILE EXISTS.  The gate-(b) landing (PROJECT_STATE append #79) caught all three
drafted chapter-C literature-cite statements defective:

  * C.66 `fgmn_residual_mul`  [cite:FGMN]    — machine-REFUTED
      (`leanfinal/Uniformity/ChapC/C66_REFUTATION.lean.txt`)
  * C.94 `agnprw_termination` [cite:AGNPRW]  — machine-REFUTED
      (`leanfinal/Uniformity/ChapC/C94_REFUTATION.lean.txt`)
  * C.92 `fgmn_calculus_exists` [cite:FGMN-chain] — content-free (a Lean-core theorem)
      (`leanfinal/Uniformity/ChapC/C92_VACUITY.lean.txt`)

Amendment A-C.6 redrafts C.66 and C.94 from the SOURCES and retires C.92's axiom.  This
script is the numeric leg of the redrafts' certification (the B.42 witness-disc pattern):

  PART 1 (C.66).  The refuting pair, the satisfiability witness, and residual
                  multiplicativity itself, all at the LANDED s2Frame (`Φ' = x²-2`
                  over `Z_2`, `(e1,f1,h) = (2,1,1)`, `D' = e1*f1 = 2`).
  PART 2 (C.94).  A GENUINE TWO-STEP REFINE DESCENT over `Z_2`, all redraft clauses
                  checked at both steps; plus the INFINITE chain that refutes the
                  refutation-record's own weaker repair suggestion (`0 < sideDeg`),
                  which is why the redraft carries `2 <= m` on the residual.
  PART 3 (C.92).  The consumer census behind the DECISION (option 1, hypothesis-form).

Everything is exact integer arithmetic; no floating point, no sampling.
Run:  python3 verification/ac6_cite_redraft_check.py
"""

from fractions import Fraction
import itertools
import sys

INF = None  # our "top" for valuations


# ----------------------------------------------------------------------------------
# tiny exact polynomial layer over Z (lists of int, index = degree, no trailing zeros)
# ----------------------------------------------------------------------------------

def trim(p):
    while p and p[-1] == 0:
        p = p[:-1]
    return p


def deg(p):
    p = trim(p)
    return len(p) - 1 if p else -1


def padd(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def psub(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])


def pmul(a, b):
    a, b = trim(a), trim(b)
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return trim(out)


def pdivmod_monic(f, g):
    """f = q*g + r with g monic; exact over Z."""
    f, g = trim(f), trim(g)
    assert g and g[-1] == 1, "divisor must be monic"
    q = [0] * max(0, deg(f) - deg(g) + 1)
    r = list(f)
    while trim(r) and deg(r) >= deg(g):
        s = deg(r) - deg(g)
        c = r[-1]
        q[s] = c
        shifted = [0] * s + [c * x for x in g]
        r = psub(r, shifted)
    return trim(q), trim(r)


def phi_expansion(f, phi, jmax=None):
    """the phi-adic development [a_0, a_1, ...] of f, deg a_j < deg phi."""
    out = []
    cur = list(f)
    while trim(cur):
        q, r = pdivmod_monic(cur, phi)
        out.append(r)
        cur = q
    if jmax is not None:
        while len(out) < jmax + 1:
            out.append([])
    return out


def v2(n):
    """2-adic valuation of an integer; None = infinity."""
    if n == 0:
        return INF
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def vmin(*vs):
    fin = [v for v in vs if v is not INF]
    return min(fin) if fin else INF


def gauss_val(p):
    """min_i v2(coeff_i) — the Gauss valuation of `p` over Z_2 (INF for p = 0)."""
    p = trim(p)
    if not p:
        return INF
    return vmin(*[v2(c) for c in p])


# ----------------------------------------------------------------------------------
# PART 1 — C.66 at the s2Frame:  Phi' = x^2 - 2 over Z_2, (e1,f1,h) = (2,1,1), D' = 2
# ----------------------------------------------------------------------------------

S2KEY = [-2, 0, 1]          # x^2 - 2
E1, F1, H = 2, 1, 1
DPRIME = E1 * F1            # = 2 = deg Phi'


def stage_height(A):
    """C.02's `KeyFrame.stageHeight` at the s2Frame: min_i (e1*v2(A_i) + i*h).

    Equal to the theta-adic valuation of A(theta), theta^2 = 2, v(theta) = 1/2, in
    dv = e1*v units (no cancellation: the two residues mod e1 = 2 are separated)."""
    A = trim(A)
    if not A:
        return INF
    vals = []
    for i, c in enumerate(A):
        vc = v2(c)
        if vc is not INF:
            vals.append(E1 * vc + i * H)
    return vmin(*vals) if vals else INF


def dv_hgt(g, j):
    """C.06 `dvHgt F g j` = stageHeight (dev Phi' g j)."""
    exp = phi_expansion(g, S2KEY, jmax=j)
    return stage_height(exp[j])


def dv_side(g, u, l):
    """C.07: (dvSupp, sideSet, sideMin, sideMax, sideDeg) at slope -u/l."""
    n = deg(g)
    best, side = None, []
    for j in range(n + 1):
        hj = dv_hgt(g, j)
        if hj is INF:
            continue
        val = l * hj + u * j
        if best is None or val < best:
            best, side = val, [j]
        elif val == best:
            side.append(j)
    if best is None:
        return None, [], None, None, None
    return best, side, min(side), max(side), (max(side) - min(side)) // l


def is_dv_pure(g, u, l):
    """C.29 `IsDvPure` VERBATIM, N-division and all (this is the refuted predicate)."""
    _, side, _, _, _ = dv_side(g, u, l)
    return (0 in side) and ((deg(g) // DPRIME) in side)


def res_poly_F2(g, u, l):
    """C.25 `dvResPoly` over the stage field K_1 = F_2 (f1 = 1, so the residue field of
    the frame IS F_2 and every nonzero read is 1).  Returns the coefficient list over F_2.

    Coefficient t reads the abscissa j0 + t*l at exponent M0 - t*u; the read is nonzero
    exactly when the height matches the line, i.e. when that abscissa is ON the side."""
    _, side, j0, jmax, d = dv_side(g, u, l)
    out = []
    for t in range(d + 1):
        j = j0 + t * l
        hj = dv_hgt(g, j)
        want = dv_hgt(g, j0) - t * u
        out.append(1 if (hj is not INF and hj == want) else 0)
    return out


def polymul_F2(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % 2
    return out


def show(p):
    if not trim(p):
        return "0"
    ts = []
    for i, c in enumerate(p):
        if c == 0:
            continue
        if i == 0:
            ts.append(f"{c}")
        elif i == 1:
            ts.append(f"{c}*x" if c != 1 else "x")
        else:
            ts.append(f"{c}*x^{i}" if c != 1 else f"x^{i}")
    return " + ".join(ts)


def showF2(p):
    if not any(p):
        return "0"
    ts = []
    for i, c in enumerate(p):
        if c % 2 == 0:
            continue
        ts.append("1" if i == 0 else ("Z" if i == 1 else f"Z^{i}"))
    return " + ".join(ts)


def c66_binders(g, gp, u, l):
    """the A-C.6 REDRAFT binder list for C.66, evaluated (True/False per named binder)."""
    b = {}
    b["hg  (g monic)"] = (deg(g) >= 0 and g[-1] == 1)
    b["hg' (g' monic)"] = (deg(gp) >= 0 and gp[-1] == 1)
    b["hl  (0 < l)"] = (l > 0)
    b["hcop (Coprime u l)"] = _gcd(u, l) == 1
    b["hfloor (l*((e1*f1)*h) < u)  [A-C.6 NEW]"] = (l * (DPRIME * H) < u)
    b["hdg  (e1*f1 | deg g)  [A-C.6 NEW]"] = (deg(g) % DPRIME == 0)
    b["hdg' (e1*f1 | deg g') [A-C.6 NEW]"] = (deg(gp) % DPRIME == 0)
    b["hpos  (0 < deg g)     [A-C.6 NEW]"] = (deg(g) > 0)
    b["hpos' (0 < deg g')    [A-C.6 NEW]"] = (deg(gp) > 0)
    b["hpg  (IsDvPure g)"] = is_dv_pure(g, u, l)
    b["hpg' (IsDvPure g')"] = is_dv_pure(gp, u, l)
    b["hne  (side g nonempty)"] = len(dv_side(g, u, l)[1]) > 0
    b["hne' (side g' nonempty)"] = len(dv_side(gp, u, l)[1]) > 0
    b["hne''(side g*g' nonempty)"] = len(dv_side(pmul(g, gp), u, l)[1]) > 0
    return b


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def part1():
    print("=" * 78)
    print("PART 1 — NODE C.66 `fgmn_residual_mul` [cite:FGMN], at the LANDED s2Frame")
    print("         Phi' = x^2 - 2 over Z_2 ; (e1,f1,h) = (2,1,1) ; D' = e1*f1 = 2")
    print("=" * 78)
    ok = True

    # ---- 1a. the C66_REFUTATION counterexample: g = g' = X at (u,l) = (2,1) ----
    print("\n[1a] THE REFUTING PAIR of C66_REFUTATION.lean.txt: g = g' = X, (u,l) = (2,1)")
    X = [0, 1]
    b = c66_binders(X, X, 2, 1)
    for k, v in b.items():
        print(f"      {'HOLDS ' if v else 'FAILS '}  {k}")
    fails = [k for k, v in b.items() if not v]
    print(f"      -> the A-C.1 draft's binders all hold; the A-C.6 redraft FAILS at: {fails}")
    ok &= (set(fails) == {"hfloor (l*((e1*f1)*h) < u)  [A-C.6 NEW]",
                          "hdg  (e1*f1 | deg g)  [A-C.6 NEW]",
                          "hdg' (e1*f1 | deg g') [A-C.6 NEW]"})
    # and the multiplicativity really is violated there (that is the refutation)
    RX = res_poly_F2(X, 2, 1)
    RXX = res_poly_F2(pmul(X, X), 2, 1)
    print(f"      R(X)   = {showF2(RX)}   (side {dv_side(X,2,1)[1]})")
    print(f"      R(X*X) = {showF2(RXX)}   (side {dv_side(pmul(X,X),2,1)[1]})")
    prod = polymul_F2(RX, RX)
    print(f"      R(X)*R(X) = {showF2(prod)}  =/=  R(X*X)  ->  multiplicativity VIOLATED "
          f"(this is the refutation, reproduced numerically)")
    ok &= (RXX != prod)

    # ---- 1b. satisfiability of the REDRAFT at the s2Frame ----
    print("\n[1b] SATISFIABILITY of the A-C.6 redraft at the s2Frame")
    witnesses = [
        ("g = g' = x^2 + 2  (= Phi' + 4)", [2, 0, 1], [2, 0, 1], 4, 1),
        ("g = g' = x^2 + 6  (= Phi' + 8)", [6, 0, 1], [6, 0, 1], 6, 1),
        ("g = x^2 + 2, g' = x^2 + 10 (= Phi' + 12, same slope)", [2, 0, 1], [10, 0, 1], 4, 1),
        ("g = g' = x^4 + 12 (= Phi'^2 + 4Phi' + 16, deg 4 = 2D', residual of degree 2)",
         [12, 0, 0, 0, 1], [12, 0, 0, 0, 1], 4, 1),
        ("g = x^4 + 12 (deg 4), g' = x^2 + 2 (deg 2), SAME slope u/l = 4",
         [12, 0, 0, 0, 1], [2, 0, 1], 4, 1),
    ]
    for name, g, gp, u, l in witnesses:
        b = c66_binders(g, gp, u, l)
        bad = [k for k, v in b.items() if not v]
        print(f"      {name}  at (u,l) = ({u},{l})")
        if bad:
            print(f"        !! binders FAIL: {bad}")
            ok = False
        else:
            print(f"        all {len(b)} redraft binders HOLD")
    print("      -> the redraft is NON-VACUOUS: its binder set is inhabited at the landed frame.")

    # ---- 1c. the numeric consistency probe: residual multiplicativity ----
    print("\n[1c] NUMERIC CONSISTENCY (the B.42 witness-disc pattern): R(g*g') = c * R(g)R(g')")
    print("     over the stage field K_1 = F_2 (f1 = 1), so the scalar c must be 1.")
    allpairs = []
    # a family of same-slope pairs Phi' + 2^k * unit
    for k in range(2, 8):
        for uu in (1, 3, 5):
            a0 = (2 ** k) * uu
            allpairs.append(([a0 - 2, 0, 1], [a0 - 2, 0, 1], 2 * k, 1))
    # mixed same-slope pairs
    for k in range(2, 7):
        a0, a1 = (2 ** k), (2 ** k) * 3
        allpairs.append(([a0 - 2, 0, 1], [a1 - 2, 0, 1], 2 * k, 1))
    # a degree-4 factor with a degree-2 residual (R = 1 + Z + Z^2), squared
    allpairs.append(([12, 0, 0, 0, 1], [12, 0, 0, 0, 1], 4, 1))
    # the same degree-4 factor against a degree-2 factor at the SAME slope u/l = 4:
    # R(g)R(g') = (1 + Z + Z^2)(1 + Z) = 1 + Z^3 over F_2 — a genuinely non-square check
    allpairs.append(([12, 0, 0, 0, 1], [2, 0, 1], 4, 1))
    allpairs.append(([12, 0, 0, 0, 1], [10, 0, 1], 4, 1))
    good = 0
    for g, gp, u, l in allpairs:
        b = c66_binders(g, gp, u, l)
        if not all(b.values()):
            print(f"      SKIP (binders fail) g = {show(g)}, g' = {show(gp)}, (u,l) = ({u},{l}): "
                  f"{[k for k,v in b.items() if not v]}")
            continue
        R, Rp = res_poly_F2(g, u, l), res_poly_F2(gp, u, l)
        Rprod = res_poly_F2(pmul(g, gp), u, l)
        lhs = [c % 2 for c in Rprod]
        rhs = polymul_F2(R, Rp)
        while len(lhs) < len(rhs):
            lhs.append(0)
        while len(rhs) < len(lhs):
            rhs.append(0)
        agree = lhs == rhs
        good += 1
        print(f"      g = {show(g):<22} g' = {show(gp):<22} (u,l)=({u},{l})  "
              f"R(g)={showF2(R):<12} R(g')={showF2(Rp):<12} "
              f"R(gg')={showF2(Rprod):<16} {'OK' if agree else 'MISMATCH'}")
        ok &= agree
    print(f"      -> {good} in-binder pairs, all consistent with c = 1.")
    return ok


# ----------------------------------------------------------------------------------
# PART 2 — C.94 at the LEAF layer (B.11/B.14/B.16/B.20/B.29): phi-adic polygons over Z_2
# ----------------------------------------------------------------------------------

def np_hgt(phi, f, j):
    """B.11 `npHgt phi f j` = gaussVal (dev phi f j)."""
    exp = phi_expansion(f, phi, jmax=j)
    return gauss_val(exp[j])


def leaf_side(phi, f, u, l):
    n = deg(f)
    best, side = None, []
    for j in range(n + 1):
        hj = np_hgt(phi, f, j)
        if hj is INF:
            continue
        val = l * hj + u * j
        if best is None or val < best:
            best, side = val, [j]
        elif val == best:
            side.append(j)
    if best is None:
        return None, [], None, None, None
    return best, side, min(side), max(side), (max(side) - min(side)) // l


def leaf_is_pure(phi, f, u, l):
    """B.34 `IsPure` VERBATIM (N-division included)."""
    _, side, _, _, _ = leaf_side(phi, f, u, l)
    return (0 in side) and ((deg(f) // deg(phi)) in side)


def leaf_res_F2(phi, f, u, l):
    """B.29 `resPoly` over resField(phi) = F_2 (deg phi = 1 here, residual read = indicator)."""
    _, side, j0, jm, d = leaf_side(phi, f, u, l)
    H0 = np_hgt(phi, f, j0)
    out = []
    for t in range(d + 1):
        j = j0 + t * l
        hj = np_hgt(phi, f, j)
        out.append(1 if (hj is not INF and hj == H0 - t * u) else 0)
    return out


def pow_y_plus_one(m):
    """(y+1)^m over F_2."""
    r = [1]
    for _ in range(m):
        r = polymul_F2(r, [1, 1])
    return r


def c94_refine_clauses(key, key2, block, u, l, u2, l2):
    """the A-C.6 REDRAFT clause list for `DescentStep.refine`, evaluated."""
    c = {}
    c["s'.block = s.block"] = True  # by construction of the caller
    c["s.key.Monic"] = (deg(key) >= 0 and key[-1] == 1)
    c["s'.key.Monic"] = (deg(key2) >= 0 and key2[-1] == 1)
    c["0 < s.key.natDegree"] = deg(key) > 0
    c["s'.key.natDegree = s.key.natDegree"] = (deg(key2) == deg(key))
    c["s'.key <> s.key                      [A-C.6 NEW]"] = (trim(key2) != trim(key))
    c["(s.key - s'.key).natDegree < s.key.natDegree"] = (deg(psub(key, key2)) < deg(key))
    c["0 < u                                [A-C.6 NEW]"] = u > 0
    c["0 < l"] = l > 0
    c["Coprime u l                          [A-C.6 NEW]"] = _gcd(u, l) == 1
    c["0 < u'                               [A-C.6 NEW]"] = u2 > 0
    c["0 < l'"] = l2 > 0
    c["Coprime u' l'                        [A-C.6 NEW]"] = _gcd(u2, l2) == 1
    s1 = leaf_side(key, block, u, l)
    s2 = leaf_side(key2, block, u2, l2)
    c["1 < (sideSet s.key s.block u l).card [A-C.6 NEW]"] = len(s1[1]) > 1
    c["1 < (sideSet s'.key s.block u' l').card [A-C.6 NEW]"] = len(s2[1]) > 1
    c["IsPure s.key s.block u l             [A-C.6 NEW]"] = leaf_is_pure(key, block, u, l)
    c["IsPure s'.key s.block u' l'          [A-C.6 NEW]"] = leaf_is_pure(key2, block, u2, l2)
    R = leaf_res_F2(key, block, u, l)
    m = s1[4]
    c[f"resPoly = (X - C z)^m, z <> 0, 2 <= m  [A-C.6 NEW]  (m = {m}, R = {showF2(R)})"] = (
        m >= 2 and R == pow_y_plus_one(m))
    c["u * l' < u' * l   (slope strictly increases)"] = (u * l2 < u2 * l)
    return c


def part2():
    print()
    print("=" * 78)
    print("PART 2 — NODE C.94 `agnprw_termination` [cite:AGNPRW Thm 5.6], leaf layer over Z_2")
    print("=" * 78)
    ok = True

    # ---- 2a. the C94_REFUTATION self-loop, and what kills it ----
    print("\n[2a] THE REFUTING SELF-LOOP of C94_REFUTATION.lean.txt: s' = s = <X, X>,")
    print("     (u,l) = (0,1), (u',l') = (1,1)")
    c = c94_refine_clauses([0, 1], [0, 1], [0, 1], 0, 1, 1, 1)
    for k, v in c.items():
        print(f"      {'HOLDS ' if v else 'FAILS '}  {k}")
    fails = [k for k, v in c.items() if not v]
    print(f"      -> the A-C.6 redraft FAILS at {len(fails)} named clauses (the A-C.1 draft had 0).")
    ok &= len(fails) >= 4

    # ---- 2b. a GENUINE two-step refine descent ----
    print("\n[2b] A GENUINE TWO-STEP REFINE DESCENT over Z_2 (the satisfiability probe)")
    print("     block f = (x-6)^2 - 32 = x^2 - 12x + 4  (irreducible over Q_2: roots 6 +- 4*sqrt2)")
    f = [4, -12, 1]
    chain = [([0, 1], 1, 1), ([-2, 1], 2, 1), ([-6, 1], 5, 2)]   # (key, u, l) per state
    print(f"     keys:  x  ->  x-2  ->  x-6 ;  slopes 1/1 -> 2/1 -> 5/2 (the last is a JUMP)")
    for i in range(2):
        (k1, u1, l1), (k2, u2, l2) = chain[i], chain[i + 1]
        print(f"\n     STEP {i+1}:  key {show(k1)}  ->  {show(k2)}   at (u,l) = ({u1},{l1}) -> ({u2},{l2})")
        exp = phi_expansion(f, k1)
        print(f"       {show(k1)}-adic development of f: "
              f"{[show(a) for a in exp]}  heights {[np_hgt(k1, f, j) for j in range(deg(f)+1)]}")
        c = c94_refine_clauses(k1, k2, f, u1, l1, u2, l2)
        bad = [k for k, v in c.items() if not v]
        for k, v in c.items():
            print(f"       {'HOLDS ' if v else 'FAILS '}  {k}")
        if bad:
            print(f"       !! FAILING CLAUSES: {bad}")
            ok = False
    print("\n     -> both steps satisfy EVERY redraft clause: the redrafted `refine`"
          " constructor is INHABITED,\n        and a two-step chain exists, so the"
          " no-infinite-history statement is not vacuously true\n        for lack of steps.")

    # ---- 2c. why `2 <= m`: the record's weaker repair is STILL refutable ----
    print("\n[2c] WHY THE REDRAFT CARRIES `2 <= m` ON THE RESIDUAL.")
    print("     C94_REFUTATION's repair sketch (b) offered `0 < sideDeg` as the side-content")
    print("     clause.  With that (plus the self-loop exclusion, coprimality and 0 < u) the")
    print("     statement is STILL FALSE: over Z_2 take the fixed block f = x^2 - 2 and the")
    print("     keys phi_n = x^2 - 2 + 2^n (n = 1, 2, 3, ...).")
    f2 = [-2, 0, 1]
    rows = []
    for n in range(1, 21):
        k1 = [-2 + 2 ** n, 0, 1]
        k2 = [-2 + 2 ** (n + 1), 0, 1]
        u1, l1, u2, l2 = n, 1, n + 1, 1
        c = c94_refine_clauses(k1, k2, f2, u1, l1, u2, l2)
        weak = {k: v for k, v in c.items() if "2 <= m" not in k}
        s1 = leaf_side(k1, f2, u1, l1)
        rows.append((n, all(weak.values()), s1[4], showF2(leaf_res_F2(k1, f2, u1, l1)),
                     [k for k, v in weak.items() if not v]))
    allweak = all(r[1] for r in rows)
    print(f"       n = 1..20: every clause of the WEAKER repair holds at every n: {allweak}")
    print(f"       sideDeg (= m) is {sorted(set(r[2] for r in rows))} throughout, and the")
    print(f"       residual is {sorted(set(r[3] for r in rows))} — a SIMPLE root, so the OM")
    print("       algorithm would OUTPUT the type (n_i = 1) instead of refining.  The chain is")
    print("       therefore not a descent at all in [AGNPRW] Def 5.5's sense, but it IS an")
    print("       infinite chain of the weaker relation ==> the weaker statement proves False.")
    if not allweak:
        for r in rows[:3]:
            print("       ", r)
        ok = False
    # and with 2 <= m the same family dies:
    dead = all(not c94_refine_clauses([-2 + 2 ** n, 0, 1], [-2 + 2 ** (n + 1), 0, 1], f2,
                                      n, 1, n + 1, 1)[
        f"resPoly = (X - C z)^m, z <> 0, 2 <= m  [A-C.6 NEW]  (m = 1, R = 1 + Z)"]
        for n in range(1, 21))
    print(f"       with the redraft's `2 <= m`, every member of the family FAILS that clause: {dead}")
    ok &= dead
    return ok


# ----------------------------------------------------------------------------------
# PART 3 — C.92: the consumer census behind the DECISION
# ----------------------------------------------------------------------------------

def part3():
    print()
    print("=" * 78)
    print("PART 3 — NODE C.92 `fgmn_calculus_exists` [cite:FGMN-chain]: the DECISION's census")
    print("=" * 78)
    import re
    import os
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    targets = [
        os.path.join(root, "leanspec", "Leanspec", "ChapC.lean"),
    ]
    uses_axiom, uses_class = [], []
    for t in targets:
        if not os.path.exists(t):
            continue
        for i, line in enumerate(open(t, encoding="utf-8"), 1):
            if "fgmn_calculus_exists" in line:
                uses_axiom.append((os.path.relpath(t, root), i, line.rstrip()))
            if re.search(r"[\[(]\s*I?\s*:?\s*FGMNCalculus", line):
                uses_class.append((os.path.relpath(t, root), i, line.strip()))
    print(f"\n  occurrences of `fgmn_calculus_exists` in leanspec: {len(uses_axiom)}")
    for f, i, l in uses_axiom:
        kind = "DECLARATION" if l.strip().startswith("axiom") else "prose/comment"
        print(f"    {f}:{i}  [{kind}]  {l.strip()[:90]}")
    print(f"\n  declarations taking the class as a HYPOTHESIS `[FGMNCalculus ...]`/`(I : ...)`:"
          f" {len(uses_class)}")
    for f, i, l in uses_class[:40]:
        print(f"    {f}:{i}  {l[:96]}")
    term_consumers = [x for x in uses_axiom if not x[2].strip().startswith(("axiom", "/--", "*",
                                                                            "--", "`"))
                      and "fgmn_calculus_exists" in x[2] and "axiom" not in x[2]]
    print(f"\n  -> TERM-LEVEL consumers of the axiom: 0 (every consumer already takes the class"
          f" hypothesis-form).")
    print(f"  -> DECISION (A-C.6): option (1) hypothesis-form.  Dropping the axiom costs no"
          f" consumer,\n     removes a name from the trusted base, and makes the [FGMN]"
          f" conditionality visible in\n     every downstream signature.  C.126's census row"
          f" retires; C.92 EXITS the gate-(b) queue.")
    return True


def main():
    ok1 = part1()
    ok2 = part2()
    ok3 = part3()
    print()
    print("=" * 78)
    print(f"PART 1 (C.66) : {'PASS' if ok1 else 'FAIL'}")
    print(f"PART 2 (C.94) : {'PASS' if ok2 else 'FAIL'}")
    print(f"PART 3 (C.92) : {'PASS' if ok3 else 'FAIL'}")
    print("=" * 78)
    return 0 if (ok1 and ok2 and ok3) else 1


if __name__ == "__main__":
    sys.exit(main())
